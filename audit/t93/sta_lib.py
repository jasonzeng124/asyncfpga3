#!/usr/bin/env python3
"""T93 (audit, own code): static timing graph of a baked gate-level netlist (netlist_baked.v + annot.sdf).

Graph model (mirrors cells/gls/prims.v + fid_core.vh, which is what the gate-level sim runs):
  * ICBUF #(.D(d)) I->O : one arc of d ps (interconnect, per sink).
  * SLICE_LUTX: arc Ak->O6 (TAkO6) / Ak->O5 (TAkO5) for every pin the LUT FUNCTION depends on (support computed
    from INIT; O5 uses INIT[31:0] and A1..A5 only).  A param missing from the instance takes the prims.v default
    (124 ps), exactly as the simulator would.  Pins in FB6/FB5 (the LUT's own output fed back) are recorded as
    feedback pins: a LUT with a feedback pin is a STATE node (C-element / latch / arbiter); arcs out of it are cut
    in the generic graph and the analyses decide explicitly which state nodes they traverse.
  * CARRY4: arcs <pin>-><out> for every arc the prims.v CARRY4 specify block has, delay = baked T<pin><out> param
    if present, else the prims.v default (the sim falls back to the same default; annot.sdf has no DI/CYINIT arcs).
    Constant pins (1'b0/1'b1) contribute nothing.
  * SELMUX2_1: D0/D1/S0 -> OUT.
  * SLICE_FFX / SLICE_LATX / PS7 / BUFG etc.: sequential or boundary; no combinational arcs (cut).
"""
import re, collections

PRIMS = '/root/wt-r90/cells/gls/prims.v'

def carry4_defaults():
    txt = open(PRIMS).read()
    i = txt.index('module CARRY4')
    blk = txt[i:txt.index('endmodule', i)]
    d = {}
    for name, val in re.findall(r'(T(?:CIN|CYINIT|DI\d|S\d)(?:CO|O)\d)=(\d+)', blk):
        d.setdefault(name, int(val))
    return d

C4DEF = carry4_defaults()
C4ARCS = []   # (pin, out, param)
for p in C4DEF:
    m = re.match(r'T(CIN|CYINIT|DI\d|S\d)((?:CO|O)\d)$', p)
    C4ARCS.append((m[1], m[2], p))

def c4_sensitizable(pin, out, sv):
    """False if a constant S pin blocks every route from pin to out (CO_i = S_i ? CO_i-1 : DI_i, O_i = S_i ^ CO_i-1)."""
    m = int(out[-1]); isco = out.startswith('CO')
    last = m if isco else m - 1             # carry muxes the signal must pass through, inclusive
    if pin in ('CIN', 'CYINIT'): first = 0; pass
    elif pin.startswith('DI'):
        j = int(pin[2:]); first = j
        if sv.get(j) == 1: return False      # mux j selects the carry, not DI
        if not isco and j == m: return False
        first = j + 1
    else:
        j = int(pin[1:])
        if not isco and j == m: return True  # S_m -> O_m (xor)
        first = j + 1                        # S_j steers mux j itself; then muxes j+1..last must pass the carry
    for i in range(first, last + 1):
        if sv.get(i) == 0: return False
    return True

CELL_RE = re.compile(r'^\s*(\w+)\s+(?:#\((.*?)\)\s+)?(\w+)\s*\((.*)\);\s*$')

def parse_params(s):
    out = {}
    if not s: return out
    for k, v in re.findall(r"\.(\w+)\(([^()]*)\)", s):
        v = v.strip()
        if "'h" in v: out[k] = int(v.split("'h")[1], 16)
        elif "'b" in v: out[k] = int(v.split("'b")[1], 2)
        elif re.fullmatch(r'-?\d+', v): out[k] = int(v)
        else: out[k] = v
    return out

def lut_support(init, out, const=None):
    """pins (1..6) the LUT function on output out ('O6'/'O5') depends on, with pins in const (k -> 0/1) fixed."""
    const = const or {}
    n = 6 if out == 'O6' else 5
    sup = set()
    for k in range(n):
        if (k + 1) in const: continue
        for a in range(1 << n):
            if a & (1 << k): continue
            if any(((a >> (j - 1)) & 1) != v for j, v in const.items() if j <= n): continue
            if ((init >> a) & 1) != ((init >> (a | (1 << k))) & 1):
                sup.add(k + 1); break
    return sup

def lut_eval(init, out, pins):
    """pins: dict k->0/1 for k in 1..6."""
    a = sum((pins.get(k, 0) & 1) << (k - 1) for k in range(1, 7))
    if out == 'O5': a &= 31
    return (init >> a) & 1

class Netlist:
    def __init__(self, path, icbuf_override=None):
        self.cells = {}          # name -> dict(type, params, pins{pin: net})
        self.ic = {}             # ICBUF name -> (I, O, D)
        self.ic_by_out = {}      # O net -> ICBUF name
        icbuf_override = icbuf_override or {}
        for line in open(path):
            if not line.startswith('  ') or line.startswith('  wire'): continue
            m = CELL_RE.match(line)
            if not m: continue
            typ, ps, name, pins = m.groups()
            params = parse_params(ps)
            pinmap = dict(re.findall(r'\.(\w+)\(([^()]+)\)', pins))
            if typ == 'ICBUF':
                d = params['D'] + icbuf_override.get(name, 0)
                self.ic[name] = (pinmap['I'], pinmap['O'], d)
                self.ic_by_out[pinmap['O']] = name
            else:
                self.cells[name] = dict(type=typ, params=params, pins=pinmap)
        self.build()

    def consts(self):
        """constant nets: PSEUDO_GND/VCC outputs, literals, ICBUF copies, LUTs whose support is all constant."""
        cv = {}
        for name, c in self.cells.items():
            if c['type'] == 'PSEUDO_GND': cv[c['pins']['Y']] = 0
            if c['type'] == 'PSEUDO_VCC': cv[c['pins']['Y']] = 1
        changed = True
        while changed:
            changed = False
            for name, (i, o, d) in self.ic.items():
                if i in cv and o not in cv: cv[o] = cv[i]; changed = True
            for name, c in self.cells.items():
                if c['type'] != 'SLICE_LUTX': continue
                out = 'O6' if 'O6' in c['pins'] else 'O5'
                onet = c['pins'][out]
                if onet in cv: continue
                const = {k: self.cval(c['pins'].get(f'A{k}'), cv) for k in range(1, 7)}
                const = {k: v for k, v in const.items() if v is not None}
                if not lut_support(c['params']['INIT'], out, const):
                    pins = dict(const)
                    cv[onet] = lut_eval(c['params']['INIT'], out, pins); changed = True
        return cv

    @staticmethod
    def cval(net, cv):
        if net is None: return None
        if net in ("1'b0", "1'h0"): return 0
        if net in ("1'b1", "1'h1"): return 1
        return cv.get(net)

    def build(self):
        self.const = cv = self.consts()
        # edges: src net -> list of (dst net, delay, kind, cell, pin)
        self.fan = collections.defaultdict(list)
        self.fin = collections.defaultdict(list)
        self.driver = {}          # net -> (cell, outpin)
        self.state_nets = {}      # net -> cell  (LUT outputs with feedback pins)
        self.fb_pins = {}         # cell -> set of feedback pin numbers
        def add(src, dst, d, kind, cell, pin):
            if src.startswith("1'b") or src.startswith("1'h"): return
            e = (src, dst, d, kind, cell, pin)
            self.fan[src].append(e); self.fin[dst].append(e)
        for name, (i, o, d) in self.ic.items():
            add(i, o, d, 'ic', name, 'I')
        for name, c in self.cells.items():
            t, p, pins = c['type'], c['params'], c['pins']
            if t == 'SLICE_LUTX':
                out = 'O6' if 'O6' in pins else 'O5'
                onet = pins[out]
                self.driver[onet] = (name, out)
                fbmask = p.get('FB6' if out == 'O6' else 'FB5', 0)
                fb = {k + 1 for k in range(6) if fbmask >> k & 1}
                const = {k: self.cval(pins.get(f'A{k}'), cv) for k in range(1, 7)}
                const = {k: v for k, v in const.items() if v is not None}
                c['out'] = out; c['support'] = lut_support(p['INIT'], out, const); c['fb'] = fb; c['const'] = const
                if fb:
                    self.state_nets[onet] = name; self.fb_pins[name] = fb
                for k in sorted(c['support']):
                    pin = f'A{k}'
                    if pin not in pins: continue
                    d = p.get(f'TA{k}{out}', 124)
                    add(pins[pin], onet, d, 'lut', name, pin)
            elif t == 'CARRY4':
                for o in ('O0','O1','O2','O3','CO0','CO1','CO2','CO3'):
                    if o in pins: self.driver[pins[o]] = (name, o)
                sv = {i: self.cval(pins.get(f'S{i}'), cv) for i in range(4)}
                for pin, out, pn in C4ARCS:
                    if pin in pins and out in pins and c4_sensitizable(pin, out, sv):
                        add(pins[pin], pins[out], p.get(pn, C4DEF[pn]), 'c4', name, pin + '>' + out)
            elif t == 'SELMUX2_1':
                self.driver[pins['OUT']] = (name, 'OUT')
                for pin, pn in (('D0', 'TD0OUT'), ('D1', 'TD1OUT'), ('S0', 'TS0OUT')):
                    add(pins[pin], pins['OUT'], p.get(pn, {'TD0OUT':104,'TD1OUT':104,'TS0OUT':273}[pn]),
                        'mux', name, pin)
            else:
                for pn, net in pins.items():
                    if pn in ('Q', 'O', 'OUT') or pn.startswith('O'):
                        self.driver[net] = (name, pn)
        for v in self.fan.values(): pass

def parse_sdf_iopaths(path):
    """instance -> {(in,out): delay} (first value of rise triple)."""
    res = collections.defaultdict(dict)
    cur = None
    for line in open(path):
        m = re.search(r'\(INSTANCE (\S+?)\)', line)
        if m: cur = m[1]
        for a, b, v in re.findall(r'\(IOPATH (\S+) (\S+) \((\d+):', line):
            res[cur][(a, b)] = int(v)
    return res

def read_names_map(path):
    site_of_c, c_of_site = {}, {}
    for l in open(path):
        if l.startswith('#'): continue
        c, s = l.split(None, 1); s = s.strip()
        site_of_c[c] = s; c_of_site[s] = c
    return site_of_c, c_of_site

def read_nets_map(path):
    wire_of_name, name_of_wire = {}, {}
    for l in open(path):
        if l.startswith('#'): continue
        w, _, n = l.strip().partition(' ')
        wire_of_name.setdefault(n, w); name_of_wire[w] = n
    return wire_of_name, name_of_wire
