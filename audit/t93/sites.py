#!/usr/bin/env python3
"""T93 (audit, own code): rule E at EVERY select site of designs A (l5_1) and B (l3_1), both corners.

Generalises rule_e.py (which checks only bridge_i.udut.ucond_br6) to every bd_steer and every bd_mux join, and
compares with the research checker's verbose output (research_skew_l{5,3}_1.txt, computed by
/root/wt-r91/cells/verify/skew.py on nextpnr's own SDF -- read here as text, never run).

    python3 sites.py              # everything: all rows, sanity checks, planted-delay test -> sites_results.{txt,json}
    python3 sites.py --depth 1    # fewer upstream (transparent-link) launches

Reads only the generated work dirs.  Never runs vvp, the project's tools or git.  Writes only in this directory.

Per (design, site gate, launch, corner) it reports, in ps, all from one common launch event (the launching link's
C node <link>.ctl.u.u at t=0):
  own    = earliest req rise at the gate's req pin, AND taps / C-elements waiting for their LAST launch-derived
           input (rule_e.py's earliest_rise), minus the latest change at the gate's select pin (longest path).
  orjoin = same, but every C-element crossed on the request path rises on its FIRST derived input (diagnostic: the
           semantics research's skew.py walk() uses when it seeds a crossed storage node with its earliest input).
  plain  = plain shortest path over every arc of the req cone (diagnostic: also ignores the delay-chain AND taps).
  r12    = own, with the select cone restricted to loop counter < 2^12 (only where the select cone holds uaddi0's
           CARRY4s; rule_e.py's slice-granular restriction, extended to every counter-carrying latch the cone uses).

Gates: bd_steer -> both fractured halves u$LUT6/u$LUT5, req pin = the pin carrying <site>_req, s pin = the other
non-constant pin.  bd_mux -> both joins uj0/uj1 (j0 = C(x_req, ctl_req.~s), j1 = C(y_req, ctl_req.s), one LUT6 each),
req pin = the pin carrying the mux's ctl_req net, s pin = the pin carrying its s net (both read from the kernel RTL,
pins found by logical net name via nets.map; cross-checked against research's pin names).

Launches per gate (method in README "## All sites"):
  direct      every link whose LATCH LUTs drive the select pin through combinational logic only (found from the
              netlist: backward walk from the s pin stopping at state nodes).  Research's launch is always one.
  upstream    for a direct launch X: every link Y whose latches drive X's latch d pins combinationally.  Checked as
              launch Y with X TRANSPARENT (X's latches traversed d->q and en->q, X's C node traversed on both sides),
              because a Muller latch is transparent while its node is high, so a late d change passes straight to
              s inside the same transaction.  Depth 2 repeats once (Z -> Y -> X).  A combination with no request path
              from the launch to the req pin is listed as such and skipped.
"""
import sys, os, re, json, collections, argparse, shutil
H = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, H)
from sta_lib import Netlist, read_names_map, read_nets_map, lut_eval

P = 'bridge_i.udut.'
DESIGNS = {
    'A': dict(item=18, rj='/root/t65/l5_1/xorshift_bench_gen_routed.json', rtl='/root/t65/l5_1/xorshift_kernel_bench.v',
              research=os.path.join(H, 'research_skew_l5_1.txt'),
              work={'worst': '/root/t65/work_l5_1_long2_worst', 'fastmin': '/root/t65/work_l5_1_long_fastmin'}),
    'B': dict(item=17, rj='/root/t65/l3_1/xorshift_bench_gen_routed.json', rtl='/root/t65/l3_1/xorshift_kernel_bench.v',
              research=os.path.join(H, 'research_skew_l3_1.txt'),
              work={'worst': '/root/t65/work_l3_1_long2_worst', 'fastmin': '/root/t65/work_l3_1_long_fastmin'}),
}
CORNERS = ('worst', 'fastmin')
GUARD_LO, GUARD_HI = 0.772, 1.155        # research's guardband, quoted in its output header; informational only
ADDER = P + 'uaddi0.'
# request-side state nodes that may be crossed (C-elements of a request rendezvous): fused-op joins, cond_br joins,
# and other muxes' joins.  Plus, per check, the C node of every TRANSPARENT link.  Never: latches, arbiters, fork /
# mux acknowledge trees, the checked gate itself (its pin is the end point).
REQ_JOIN_RE = re.compile(r'\.ujoin\.|_j\.|\.uj[01]$')
# 32-bit nets that carry the loop counter i (n7 = mux(n6, n_trueResult_6), n29 = n7 + 1, n30__* = forks of n29)
COUNTER_NET_RE = re.compile(r'\.(n7|n7_u|n6|n6_u|n_trueResult_6|n_trueResult_6_u|n29|n30__0|n30__1|n30__1_u)_data\[(\d+)\]$')


# --------------------------------------------------------------------------------------------- research output --
def parse_research(path):
    out, cur = [], None
    for line in open(path):
        m = re.match(r'\s+(VIOLATED|ok)\s+(bd_steer|bd_mux)\s+(\S+)', line)
        if m:
            cur = dict(status=m[1], kind=m[2], site=m[3][len(P):]); out.append(cur); continue
        if cur is None: continue
        m = re.match(r'\s+launch\s+(\S+)/\w+', line)
        if m: cur['launch'] = m[1][len(P):].removesuffix('.ctl.u.u'); continue
        m = re.match(r'\s+req\s+(\S+)/(A\d)', line)
        if m: cur['gate'] = m[1][len(P):]; cur['req_pin'] = m[2]; continue
        m = re.match(r'\s+sel\s+(\S+)/(A\d)', line)
        if m: cur['sel_gate'] = m[1][len(P):]; cur['sel_pin'] = m[2]; continue
        m = re.match(r'\s+earliest\s+(-?\d+) ps, (\d+)', line)
        if m: cur['earliest'] = int(m[1]); cur['req_cross'] = int(m[2]); continue
        m = re.match(r'\s+latest\s+(-?\d+) ps, (\d+)', line)
        if m: cur['latest'] = int(m[1]); cur['sel_cross'] = int(m[2]); continue
        m = re.match(r'\s+margin\s+([+-]?\d+) ps raw, ([+-]?\d+) ps guarded', line)
        if m: cur['raw'] = int(m[1]); cur['guarded'] = int(m[2]); cur = None
    # de-duplicate (the l3_1 file repeats its last block after the summary)
    seen, res = set(), []
    for r in out:
        k = (r['site'], r['gate'])
        if k in seen: continue
        seen.add(k); res.append(r)
    return res


def parse_rtl(path):
    """site -> dict(kind, req_net, s_net) from the kernel RTL (logical channel names)."""
    txt = open(path).read()
    # alias classes from plain wire assigns (assign a = b;), so a channel's data net matches whatever single
    # name nextpnr kept for it (e.g. n32__3_data == n31_data)
    parent = {}
    def find(x):
        while parent.get(x, x) != x: x = parent[x]
        return x
    for a_, b_ in re.findall(r'assign\s+(\w+)\s*=\s*(\w+)\s*;', txt):
        parent[find(a_)] = find(b_)
    sites = {'__alias__': find}
    for m in re.finditer(r'bd_steer\s+(\w+)\s*\((.*?)\);', txt, re.S):
        s = re.search(r'\.s\((\w+)\[0\]\)', m[2])[1]
        sites[m[1]] = dict(kind='bd_steer', req_net=m[1] + '_req', s_net=s.replace('_data', '_data[0]'))
    for m in re.finditer(r'bd_mux\s+#\(.*?\)\s+(\w+)\s*\((.*?)\);', txt, re.S):
        ctl = re.search(r'\.ctl_req\((\w+)\)', m[2])[1]
        s = re.search(r'\.s\((\w+)\[0\]\)', m[2])[1]
        sites[m[1]] = dict(kind='bd_mux', req_net=ctl, s_net=s.replace('_data', '_data[0]'))
    return sites


# ----------------------------------------------------------------------------------------------------- engine --
class Engine:
    def __init__(self, work, rj, netlist=None):
        self.nl = nl = Netlist(netlist or (work + '/netlist_baked.v'))
        self.site_of_c, c_of_site = read_names_map(work + '/names.map')
        _, self.name_of_wire = read_nets_map(work + '/nets.map')
        m = list(json.load(open(rj))['modules'].values())[0]
        self.lname, self.cof, self.outbits = {}, {}, {}
        bitnames = collections.defaultdict(set)
        for n, v in m['netnames'].items():
            for b in v['bits']: bitnames[b].add(n)
        for cn, c in m['cells'].items():
            bel = c['attributes'].get('NEXTPNR_BEL')
            if bel in c_of_site:
                self.lname[c_of_site[bel]] = cn; self.cof[cn] = c_of_site[bel]
                outs = [b for p_, bb in c['connections'].items() if c.get('port_directions', {}).get(p_) == 'output'
                        for b in bb if isinstance(b, int)]
                self.outbits[c_of_site[bel]] = sorted(n for b in outs for n in bitnames[b])
        del m, bitnames
        self.state_cells = set(nl.state_nets.values())
        self.latch_link = {}            # latch cell -> link path (without P)
        for c in self.state_cells:
            ln = self.L(c)
            if ln.startswith(P) and '.lat.' in ln: self.latch_link[c] = ln[len(P):].split('.lat.')[0]
        self.join_cells = {c for c in self.state_cells if REQ_JOIN_RE.search(self.L(c))}
        # bd_steer gate LUTs make REQUESTS (req.s / req.~s); a data/select walk never passes through one
        # en pin of every latch LUT (the pin fed by its own link's C node).  The LAUNCH link's latches are entered
        # only through it (their d is the upstream sender's, not caused by this launch); see check()
        self.en_pin, self.en_only = {}, set()
        for c, link in self.latch_link.items():
            cn = self.ctl_cell(link)
            if cn is None: continue
            cnet = self.out_net(cn); cc = nl.cells[c]
            ks = [k for k in cc['support'] if k not in cc['fb'] and self.src_of(cc['pins'][f'A{k}']) == cnet]
            if len(ks) == 1: self.en_pin[c] = ks[0]
        self.steer_gates = {c for c in nl.cells if re.search(r'\.ucond_br\d+\.u\$LUT[56]$', self.L(c))}
        # pins of a state LUT through which a 0->1 input can raise the output from 0 (feedback held at 0).  A
        # link controller C(req_in, ~c_next) is entered only through req_in: a rising c_next (the downstream
        # acknowledge) can only make the node FALL, which closes the latch and starts no forward wave.
        self.pos_pins = {}
        for c in self.state_cells:
            cc = nl.cells[c]; init = cc['params']['INIT']; out = cc['out']
            sup = [k for k in sorted(cc['support']) if k not in cc['fb']]
            pos = set()
            for k in sup:
                others = [j for j in sup if j != k]
                for a_ in range(1 << len(others)):
                    pins = {j: (a_ >> i) & 1 for i, j in enumerate(others)}
                    pins.update(cc['const'])
                    for f in cc['fb']: pins[f] = 0
                    pins[k] = 0; v0 = lut_eval(init, out, pins)
                    pins[k] = 1; v1 = lut_eval(init, out, pins)
                    if v0 == 0 and v1 == 1: pos.add(k); break
            self.pos_pins[c] = pos

    def L(self, c): return self.lname.get(c, '?' + self.site_of_c.get(c, c))
    def src_of(self, net):
        icn = self.nl.ic_by_out.get(net)
        return self.nl.ic[icn][0] if icn else net
    def lognet(self, net): return self.name_of_wire.get(self.src_of(net), '?')
    def ctl_cell(self, link): return self.cof.get(P + link + '.ctl.u.u')
    def link_latches(self, link): return {c for c, l in self.latch_link.items() if l == link}
    def out_net(self, c): return self.nl.cells[c]['pins'][self.nl.cells[c]['out']]

    # -- gate pins, by logical net name --
    def gate_pins(self, gate, req_net, s_net, alias=lambda x: x):
        c = self.cof.get(P + gate)
        if c is None: return None
        cc = self.nl.cells[c]
        rp = sp = None
        for k in sorted(cc['support']):
            if k in cc['fb']: continue
            net = cc['pins'][f'A{k}']; ln = self.lognet(net)
            if not ln.startswith(P): continue
            ln = alias(re.sub(r'\[0\]$', '', ln[len(P):]))
            if ln == alias(req_net): rp = (f'A{k}', net)
            elif ln == alias(re.sub(r'\[0\]$', '', s_net)): sp = (f'A{k}', net)
        return c, rp, sp

    # -- the graph walks (rule_e.py's, parameterised by the allowed state cells) --
    def arcs_ok(self, e, allowed, excluded):
        src, dst, d, kind, cell, pin = e
        if cell in excluded: return False
        if kind == 'lut':
            if int(pin[1:]) in self.nl.cells[cell]['fb']: return False
            if cell in self.state_cells:
                if cell not in allowed: return False
                if cell in self.en_only and int(pin[1:]) != self.en_pin.get(cell): return False
                if int(pin[1:]) not in self.pos_pins[cell]: return False
        return True

    def cone(self, start, end, allowed, excluded=frozenset()):
        nl = self.nl
        fw, stk = set(), [start]
        while stk:
            n = stk.pop()
            if n in fw: continue
            fw.add(n)
            for e in nl.fan[n]:
                if self.arcs_ok(e, allowed, excluded): stk.append(e[1])
        bw, stk = set(), [end]
        while stk:
            n = stk.pop()
            if n in bw or n not in fw: continue
            bw.add(n)
            for e in nl.fin[n]:
                if self.arcs_ok(e, allowed, excluded): stk.append(e[0])
        return bw

    def topo(self, cn, allowed, excluded):
        indeg = {n: 0 for n in cn}
        edges = collections.defaultdict(list)
        for n in cn:
            for e in self.nl.fan[n]:
                if e[1] in cn and self.arcs_ok(e, allowed, excluded):
                    edges[n].append(e); indeg[e[1]] += 1
        q = [n for n in cn if indeg[n] == 0]; order = []
        while q:
            n = q.pop(); order.append(n)
            for e in edges[n]:
                indeg[e[1]] -= 1
                if indeg[e[1]] == 0: q.append(e[1])
        if len(order) != len(cn):
            left = set(cn) - set(order)
            cells = sorted({self.L(e[4])[len(P):] for n in left for e in self.nl.fin[n]
                            if e[0] in left and e[3] == 'lut' and e[4] in self.state_cells})
            raise RuntimeError(f'cycle in cone: {len(left)} nets not ordered; state cells on it: {cells[:12]}')
        return order, edges

    def longest(self, start, end, allowed, excluded=frozenset()):
        cn = self.cone(start, end, allowed, excluded)
        if end not in cn: return None, [], cn
        order, edges = self.topo(cn, allowed, excluded)
        arr = {start: 0}; pred = {}
        for n in order:
            if n not in arr: continue
            for e in edges[n]:
                t = arr[n] + e[2]
                if t > arr.get(e[1], -1): arr[e[1]] = t; pred[e[1]] = e
        path, n = [], end
        while n in pred: path.append(pred[n]); n = pred[n][0]
        return arr[end], path[::-1], cn

    def earliest_rise(self, start, end, allowed, or_cells=frozenset()):
        """rule_e.py's earliest_rise; a state cell in or_cells rises on its FIRST derived input (diagnostic)."""
        nl = self.nl
        cn = self.cone(start, end, allowed)
        if end not in cn: return None, [], cn, []
        order, edges = self.topo(cn, allowed, frozenset())
        arr = {start: 0}; pred = {}; notes = []
        for n in order:
            if n == start: continue
            ins = [e for e in nl.fin[n] if e[0] in cn and self.arcs_ok(e, allowed, frozenset())]
            if not ins: continue
            kind = ins[0][3]
            if kind == 'ic':
                e = ins[0]; arr[n] = arr[e[0]] + e[2]; pred[n] = [e]; continue
            if kind != 'lut':
                e = min(ins, key=lambda e: arr[e[0]] + e[2]); arr[n] = arr[e[0]] + e[2]; pred[n] = [e]
                notes.append(f'non-LUT {e[4]} on req path, plain min'); continue
            cell = ins[0][4]; cc = nl.cells[cell]; out = cc['out']; init = cc['params']['INIT']
            D = {int(e[5][1:]): e for e in ins}
            fb = cc['fb']
            free = [k for k in cc['support'] if k not in D and k not in fb]
            best = None
            for na in range(1 << len(free)):
                base = {k: (na >> i) & 1 for i, k in enumerate(free)}
                base.update(cc['const'])
                for f in fb: base[f] = 0
                pins0 = dict(base)
                for k in D: pins0[k] = 0
                if lut_eval(init, out, pins0) != 0: continue
                Dk = sorted(D)
                for s in range(1, 1 << len(Dk)):
                    pins = dict(pins0)
                    S = [Dk[i] for i in range(len(Dk)) if s >> i & 1]
                    for k in S: pins[k] = 1
                    if lut_eval(init, out, pins) != 1: continue
                    t = max(arr[D[k][0]] + D[k][2] for k in S)
                    if best is None or t < best[0]: best = (t, [D[k] for k in S], base)
            if cell in or_cells:
                e = min(D.values(), key=lambda e: arr[e[0]] + e[2]); best = (arr[e[0]] + e[2], [e], {})
            if best is None:
                raise RuntimeError(f'req cone LUT {cell} {self.L(cell)} cannot rise under the 0->1 assumption')
            arr[n] = best[0]; pred[n] = best[1]
            if len(D) > 1 and cell in self.state_cells:
                notes.append(f'{self.L(cell)[len(P):]}: derived {sorted(D)}, arrivals+arc '
                             f'{dict((f"A{k}", arr[D[k][0]] + D[k][2]) for k in sorted(D))}, rises at {best[0]}')
        path, n = [], end
        while n in pred:
            e = max(pred[n], key=lambda e: arr[e[0]] + e[2]); path.append(e); n = e[0]
        return arr.get(end), path[::-1], cn, notes

    def plain_min(self, start, end, allowed):
        cn = self.cone(start, end, allowed)
        if end not in cn: return None
        order, edges = self.topo(cn, allowed, frozenset())
        arr = {start: 0}
        for n in order:
            if n not in arr: continue
            for e in edges[n]:
                t = arr[n] + e[2]
                if t < arr.get(e[1], 1 << 60): arr[e[1]] = t
        return arr.get(end)

    # -- launch discovery --
    def state_sources(self, nets):
        """state cells (and undriven / non-LUT sources) reaching any of `nets` through combinational arcs only."""
        nl = self.nl
        seen, stk, srcs, other = set(), list(nets), set(), set()
        while stk:
            n = stk.pop()
            if n in seen: continue
            seen.add(n)
            if n in nl.state_nets: srcs.add(nl.state_nets[n]); continue
            ins = [e for e in nl.fin[n] if not (e[3] == 'lut' and int(e[5][1:]) in nl.cells[e[4]]['fb'])
                   and e[4] not in self.steer_gates]
            if not ins and n in nl.driver: other.add(nl.driver[n][0])
            for e in ins: stk.append(e[0])
        return srcs, other

    def upstream_links(self, link):
        """links whose latches drive `link`'s latch d pins combinationally; plus non-latch sources (names)."""
        ctl = self.ctl_cell(link); cnet = self.out_net(ctl)
        dnets = []
        for c in self.link_latches(link):
            cc = self.nl.cells[c]
            for k in cc['support']:
                if k in cc['fb']: continue
                net = cc['pins'][f'A{k}']
                if self.src_of(net) == cnet: continue           # en pin
                dnets.append(net)
        srcs, other = self.state_sources(dnets)
        ups = sorted({self.latch_link[c] for c in srcs if c in self.latch_link} - {link})
        nonlatch = sorted({self.L(c)[len(P):] if self.L(c).startswith(P) else ("FF (outside udut)" if "$auto$ff" in self.L(c) else self.L(c))
                           for c in (srcs - set(self.latch_link)) | other if 'PACKER' not in self.L(c)})
        return ups, nonlatch

    # -- counter restriction (rule_e.py's adder_restrict, generalised to every counter-carrying latch allowed) --
    def adder_restrict(self, nbits, latches):
        k = (nbits + 3) // 4
        excl = set()
        for c, cc in self.nl.cells.items():
            if cc['type'] != 'CARRY4': continue
            mm = re.search(r'slice\[(\d+)\]', self.L(c))
            if self.L(c).startswith(ADDER) and mm and int(mm[1]) >= k: excl.add(c)
        for c in latches:
            bs = {int(m[2]) for n in self.outbits.get(c, []) for m in [COUNTER_NET_RE.search(n)] if m}
            if len(bs) > 1: raise RuntimeError(f'latch {self.L(c)} drives several counter bits {bs}')
            if bs and bs.pop() >= nbits: excl.add(c)
        return excl

    # -- one check --
    def check(self, gate_cell, rp, sp, launch, transparent=(), bits=(11, 12), legacy_s=False):
        nl = self.nl
        lc = self.ctl_cell(launch)
        if lc is None: return dict(error=f'no C node for {launch}')
        lnet = self.out_net(lc)
        lat = self.link_latches(launch)
        tlat, tctl = set(), set()
        for t in transparent:
            tlat |= self.link_latches(t); tctl.add(self.ctl_cell(t))
        missing = [c for c in lat if c not in self.en_pin]
        if missing: return dict(error=f'no en pin found for {len(missing)} launch latch LUTs')
        self.en_only = lat
        try:
            return self._check(gate_cell, rp, sp, launch, lnet, lat, tlat, tctl, transparent, bits, legacy_s)
        finally:
            self.en_only = set()

    def _check(self, gate_cell, rp, sp, launch, lnet, lat, tlat, tctl, transparent, bits, legacy_s):
        nl = self.nl
        req_allowed = (self.join_cells | tctl) - {gate_cell}
        s_allowed = lat | tlat
        if transparent and not legacy_s:
            s_allowed = s_allowed | tctl | req_allowed           # en path of the transparent link(s)
        smax, spath, scone = self.longest(lnet, sp[1], s_allowed, excluded=self.steer_gates)
        if smax is None: return dict(error='launch does not reach the select pin')
        rmin, rpath, rcone, notes = self.earliest_rise(lnet, rp[1], req_allowed)
        if rmin is None: return dict(error='no request path from the launch to the req pin', s_max=smax)
        crossed = sorted({e[4] for n in rcone for e in nl.fin[n] if e[0] in rcone and e[4] in req_allowed})
        ror = self.earliest_rise(lnet, rp[1], req_allowed, or_cells=set(crossed))[0]
        rpl = self.plain_min(lnet, rp[1], req_allowed)
        scells = {e[4] for n in scone for e in nl.fin[n] if e[0] in scone and e[3] != 'ic'}
        has_adder = any(nl.cells[x]['type'] == 'CARRY4' and self.L(x).startswith(ADDER) for x in scells)
        r = dict(s_max=smax, req_min=rmin, own=rmin - smax, orjoin=ror - smax, plain=rpl - smax,
                 req_orjoin=ror, req_plain=rpl, crossed=[self.L(x)[len(P):] for x in crossed],
                 has_adder=has_adder, notes=notes, s_path=self.fmt_path(spath), req_path=self.fmt_path(rpath),
                 s_crit_ic=[e[4] for e in spath if e[3] == 'ic'], req_crit_ic=[e[4] for e in rpath if e[3] == 'ic'],
                 restricted={})
        if transparent and not legacy_s:
            r['s_max_legacy'] = self.longest(lnet, sp[1], lat | tlat, excluded=self.steer_gates)[0]
        for b in bits:
            if not has_adder: r['restricted'][b] = r['own']; continue
            excl = self.adder_restrict(b, s_allowed & set(self.latch_link)) | self.steer_gates
            smk = self.longest(lnet, sp[1], s_allowed, excluded=excl)[0]
            r['restricted'][b] = rmin - smk if smk is not None else None
        return r

    def fmt_path(self, path):
        out, t = [], 0
        for e in path:
            t += e[2]
            if e[3] == 'ic': continue
            out.append(f'{t:7d}  {e[4]} {e[5]:<8s} +{e[2]:4d}  {self.L(e[4])[len(P):]}')
        return out


# ---------------------------------------------------------------------------------------------------- driver --
def enumerate_launches(eng, sp_net, research_launch, depth):
    """[(launch, transparent tuple, how)] for one gate, plus notes."""
    srcs, other = eng.state_sources([sp_net])
    direct = sorted({eng.latch_link[c] for c in srcs if c in eng.latch_link})
    notes = []
    nonlatch = sorted({eng.L(c) for c in (srcs - set(eng.latch_link)) | other if 'PACKER' not in eng.L(c)})
    if nonlatch: notes.append(f'select cone has non-latch sources {nonlatch}')
    if research_launch and research_launch not in direct:
        notes.append(f'research launch {research_launch} is NOT a direct latch source of the select: {direct}')
    out = [(l, (), 'direct') for l in direct]
    frontier = [(l, ()) for l in direct]
    for d in range(depth):
        nxt = []
        for x, tr in frontier:
            ups, nonl = eng.upstream_links(x)
            if nonl: notes.append(f'{x} latch d also from non-latch sources {nonl} (not launched)')
            for y in ups:
                if y in tr or any(y == o[0] and o[1] == (x,) + tr for o in out): continue
                cand = (y, (x,) + tr, f'upstream-{d + 1}')
                out.append(cand); nxt.append((y, (x,) + tr))
        frontier = nxt
    return out, notes


def run_design(des, depth, corners=CORNERS):
    cfg = DESIGNS[des]
    research = parse_research(cfg['research'])
    rtl = parse_rtl(cfg['rtl'])
    rows, notes = [], []
    for corner in corners:
        eng = Engine(cfg['work'][corner], cfg['rj'])
        for rr in research:
            site = rr['site']; info = rtl[site]
            gate = rr['gate']
            if rr.get('sel_gate') != gate: notes.append(f'{des} {gate}: research req/sel on different gates')
            gp = eng.gate_pins(gate, info['req_net'], info['s_net'], rtl['__alias__'])
            if gp is None or gp[1] is None or gp[2] is None:
                notes.append(f'{des} {corner} {gate}: could not map pins {gp}'); continue
            gc, rp, sp = gp
            if corner == corners[0]:
                notes.append(f'{des} {gate}: pins by net name req {rp[0]} s {sp[0]} '
                             + ('== research' if (rp[0], sp[0]) == (rr['req_pin'], rr['sel_pin']) else '!= research'))
            if corner == corners[0] and (rp[0] != rr['req_pin'] or sp[0] != rr['sel_pin']):
                notes.append(f'{des} {gate}: pins by net name req {rp[0]} s {sp[0]} differ from research '
                             f'req {rr["req_pin"]} sel {rr["sel_pin"]}')
            launches, lnotes = enumerate_launches(eng, sp[1], rr['launch'], depth)
            if corner == corners[0]:
                notes += [f'{des} {gate}: {x}' for x in lnotes]
            for launch, tr, how in launches:
                try:
                    r = eng.check(gc, rp, sp, launch, tr)
                except RuntimeError as ex:
                    r = dict(error=str(ex))
                row = dict(design=des, corner=corner, kind=info['kind'], site=site, gate=gate,
                           req_pin=rp[0], s_pin=sp[0], launch=launch, transparent=list(tr), how=how,
                           research_launch=(launch == rr['launch'] and not tr),
                           research_raw=rr['raw'], research_guarded=rr['guarded'], research_status=rr['status'],
                           research_req=rr['earliest'], research_sel=rr['latest'], **r)
                if 'own' in r:
                    row['own_guarded'] = round(GUARD_LO * r['req_min'] - GUARD_HI * r['s_max'])
                    row['orjoin_guarded'] = round(GUARD_LO * r['req_orjoin'] - GUARD_HI * r['s_max'])
                rows.append(row)
        del eng
    return rows, notes


def fmt_row(r):
    tr = ('  T=' + ','.join(r['transparent'])) if r['transparent'] else ''
    lab = f"{r['design']} {r['gate']:<18s} {r['corner']:<7s} {r['launch'] + tr:<62s}"
    if 'own' not in r:
        return f"{lab} -- {r['error']}"
    r12 = r['restricted'][12]
    r12s = f"{r12:>6}" if r['has_adder'] else '     ='
    rs = f"{r['research_raw']:>+6}" if r['research_launch'] and r['corner'] == 'worst' else (
        f"({r['research_raw']:>+5})" if r['corner'] == 'worst' else '')
    return (f"{lab} s {r['s_max']:>6} req {r['req_min']:>6}  OWN {r['own']:>6}  <2^12 {r12s}  OR {r['orjoin']:>6}"
            f"  plain {r['plain']:>6}  | research raw {rs}")


def summarise(rows):
    lines = []
    ok = [r for r in rows if 'own' in r]
    by_site = collections.defaultdict(list)
    for r in ok: by_site[(r['design'], r['site'])].append(r)
    lines.append('per site: min over gates (LUT5/LUT6 or uj0/uj1) and launches, per corner; '
                 'research = its raw / guarded margin at its own launch (nextpnr SDF)')
    lines.append(f"{'site':<14s} {'research':>16s} {'st':<4s} | {'own worst':>9s} {'own fmin':>8s} | "
                 f"{'own@rl worst':>12s} {'OR@rl worst':>11s} {'OR@rl fmin':>10s} | {'min OR (any)':>12s} | "
                 f"{'<2^12 worst':>11s} | binding launch (own, worst)")
    neg_own, or_only, both, research_neg = [], [], [], []
    for (des, site), rs in sorted(by_site.items()):
        def mn(f, corner=None, rl=False):
            v = [x[f] for x in rs if (corner is None or x['corner'] == corner) and (not rl or x['research_launch'])]
            return min(v) if v else None
        ow, of = mn('own', 'worst'), mn('own', 'fastmin')
        orw_rl, orf_rl = mn('orjoin', 'worst', True), mn('orjoin', 'fastmin', True)
        own_rl = mn('own', 'worst', True)
        orany = mn('orjoin')
        r12w = min(x['restricted'][12] for x in rs if x['corner'] == 'worst')
        bind = min((x for x in rs if x['corner'] == 'worst'), key=lambda x: x['own'])
        b = bind['launch'] + (' T=' + ','.join(bind['transparent']) if bind['transparent'] else '')
        rraw = min(x['research_raw'] for x in rs); rg = min(x['research_guarded'] for x in rs)
        st = 'VIOL' if any(x['research_status'] == 'VIOLATED' for x in rs) else 'ok'
        lines.append(f"{des} {site:<12s} {rraw:>+7} / {rg:>+6} {st:<4s} | {ow:>9} {of:>8} | {own_rl:>12} {orw_rl:>11} "
                     f"{orf_rl:>10} | {orany:>12} | {r12w:>11} | {b}")
        if min(ow, of) < 0: neg_own.append((des, site, ow, of, b))
        if st == 'VIOL' or rraw < 0:
            research_neg.append((des, site))
            orneg = min(orw_rl, orf_rl) < 0
            ownneg = min(ow, of) < 0
            if orneg and not ownneg: or_only.append((des, site))
            if orneg and ownneg: both.append((des, site))
    # research's VIOLATED verdict is on its GUARDED margin (0.772*req - 1.155*sel over the whole launch-to-pin span).
    # Same guard applied to our own and OR-join numbers at research's launch, per corner (informational: the
    # worst-corner SDF is already derated, so guarding it double-counts).
    lines.append('')
    lines.append("research's guard (0.772*req - 1.155*sel) applied to our numbers at research's launch, min over gates:")
    lines.append(f"{'site':<14s} {'research':>9s} | {'own_g worst':>11s} {'own_g fmin':>10s} | {'OR_g worst':>10s} {'OR_g fmin':>9s} | class")
    gcls = collections.defaultdict(list)
    for (des, site), rs in sorted(by_site.items()):
        rl = [x for x in rs if x['research_launch']]
        if not rl: continue
        g = lambda f, c: min(x[f] for x in rl if x['corner'] == c)
        ogw, ogf, rgw, rgf = g('own_guarded', 'worst'), g('own_guarded', 'fastmin'), g('orjoin_guarded', 'worst'), g('orjoin_guarded', 'fastmin')
        rg = min(x['research_guarded'] for x in rs)
        if rg >= 0: cls = 'research ok'
        elif min(ogw, ogf) < 0 and min(rgw, rgf) < 0: cls = 'guarded-negative under both own and OR-join'
        elif min(rgw, rgf) < 0: cls = 'guarded-negative only under OR-join'
        else: cls = 'guarded >= 0 under both (research flag = its SDF/launch, not reproduced)'
        gcls[cls].append(f'{des} {site}')
        lines.append(f"{des} {site:<12s} {rg:>+9} | {ogw:>11} {ogf:>10} | {rgw:>10} {rgf:>9} | {cls}")
    return lines, neg_own, or_only, both, research_neg, gcls


LEGACY_ENG = {}


def sanity_br6(rows):
    """ucond_br6 rows vs results.txt (rule_e.py's run)."""
    old = {}
    for l in open(os.path.join(H, 'results.txt')):
        m = re.match(r'(\w) (main|combined|other operand): launch (\S+?)(?:,| |$).*?\s(worst|fastmin)\s+(u\$LUT\d)'
                     r'.*?MARGIN\s+(-?\d+)\s+<2\^11\s+(-?\d+)\s+<2\^12\s+(-?\d+).*?OR-join\s+(-?\d+)\s+plain-min\s+(-?\d+)', l)
        if not m: continue
        des, kind, launch, corner, lut = m[1], m[2], m[3], m[4], m[5]
        tr = ('ulink_n30__1',) if kind == 'combined' else ()
        old[(des, launch, tr, corner, lut)] = tuple(int(m[i]) for i in (6, 8, 9, 10))
    out, allok = [], True
    for k, v in sorted(old.items()):
        des, launch, tr, corner, lut = k
        rs = [r for r in rows if r['design'] == des and r['gate'] == 'ucond_br6.' + lut and r['corner'] == corner
              and r['launch'] == launch and tuple(r['transparent']) == tr and 'own' in r]
        if not rs:
            out.append(f'  {k}: results.txt {v}  -- no sites.py row'); allok = False; continue
        r = rs[0]
        new = (r['own'], r['restricted'][12], r['orjoin'], r['plain'])
        leg = ''
        if 's_max_legacy' in r and r['s_max_legacy'] != r['s_max']:
            leg = f'  (s_max {r["s_max"]} vs latches-only {r["s_max_legacy"]}: en path of the transparent link)'
        same = new == v
        if tr and not same:
            # re-run in rule_e.py's latches-only select mode: must reproduce results.txt exactly
            eng = LEGACY_ENG.setdefault((des, corner), Engine(DESIGNS[des]['work'][corner], DESIGNS[des]['rj']))
            rtl = parse_rtl(DESIGNS[des]['rtl'])
            gc, rp, sp = eng.gate_pins('ucond_br6.' + lut, rtl['ucond_br6']['req_net'], rtl['ucond_br6']['s_net'], rtl['__alias__'])
            lg = eng.check(gc, rp, sp, launch, tr, legacy_s=True)
            lgv = (lg['own'], lg['restricted'][12], lg['orjoin'], lg['plain'])
            leg += f'; latches-only mode {lgv} {"EQUAL" if lgv == v else "DIFFERENT"}'
            same_legacy = lgv == v
        else:
            same_legacy = same
        allok &= same_legacy
        out.append(f"  {des} {launch}{' T=' + tr[0] if tr else ''} {corner:<7s} {lut}: results.txt "
                   f"own/<2^12/OR/plain {v}  sites.py {new}  {'EQUAL' if same else 'DIFFERENT'}{leg}")
    return out, allok


def plant_test():
    """Planted delay on a site other than ucond_br6: design A, worst, ucond_br3 (launch ulink_n1__1) and
    umux0 (launch ulink_n12__0).  +2000 ps on an ICBUF of the critical select path must lower the margin by
    exactly 2000 at that gate; +2000 on an ICBUF of the critical request path must raise it by 2000 (unless another
    req path takes over, in which case by less); a far-away ICBUF must change nothing."""
    cfg = DESIGNS['A']; src = cfg['work']['worst']
    rtl = parse_rtl(cfg['rtl'])
    eng = Engine(src, cfg['rj'])
    cases = []
    for site, gate, launch in (('ucond_br3', 'ucond_br3.u$LUT6', 'ulink_n1__1'), ('umux0', 'umux0.uj0', 'ulink_n12__0')):
        gc, rp, sp = eng.gate_pins(gate, rtl[site]['req_net'], rtl[site]['s_net'], rtl['__alias__'])
        base = eng.check(gc, rp, sp, launch)
        s_ic = base['s_crit_ic'][len(base['s_crit_ic']) // 2]
        r_ic = base['req_crit_ic'][len(base['req_crit_ic']) // 2]
        cases.append((site, gate, launch, base, [(s_ic, 'critical select path', -2000), (r_ic, 'critical request path', +2000)]))
    far = 'ic_012664'      # ICBUF into ucond_br6's LUT6 s pin (rule_e.py's plant): unrelated to both gates
    pd = os.path.join(H, '_plant_sites')
    os.makedirs(pd, exist_ok=True)
    for f in ('names.map', 'nets.map'):
        if not os.path.exists(os.path.join(pd, f)): os.symlink(os.path.join(src, f), os.path.join(pd, f))
    txt = open(os.path.join(src, 'netlist_baked.v')).read()
    del eng
    lines = []
    todo = [(c, ic, why, exp) for c in cases for ic, why, exp in c[4]] + [(c, far, 'unrelated ICBUF (ucond_br6 LUT6 s)', 0) for c in cases]
    for (site, gate, launch, base, _), ic, why, exp in todo:
        m = re.search(r'ICBUF #\(\.D\((\d+)\)\) ' + ic + r' ', txt)
        d0 = int(m[1])
        open(os.path.join(pd, 'netlist_baked.v'), 'w').write(txt.replace(m[0], f'ICBUF #(.D({d0 + 2000})) {ic} ', 1))
        e2 = Engine(pd, cfg['rj'])
        gc, rp, sp = e2.gate_pins(gate, rtl[site]['req_net'], rtl[site]['s_net'], rtl['__alias__'])
        r = e2.check(gc, rp, sp, launch)
        d = r['own'] - base['own']
        ok = (d == exp) if exp <= 0 else (0 < d <= exp)
        lines.append(f"  PLANT {ic} +2000 ps ({why}) at A worst {gate} launch {launch}: own {base['own']} -> {r['own']} "
                     f"(delta {d:+d}, expected {exp:+d}{' or less' if exp > 0 else ''}) {'PASS' if ok else 'FAIL'};"
                     f" OR {base['orjoin']} -> {r['orjoin']}, plain {base['plain']} -> {r['plain']}")
        del e2
    shutil.rmtree(pd)
    return lines


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--depth', type=int, default=2)
    ap.add_argument('--no-plant', action='store_true')
    a = ap.parse_args()
    rows, notes = [], []
    for des in ('A', 'B'):
        r, n = run_design(des, a.depth)
        rows += r; notes += n
        print(f'design {des}: {len(r)} rows', file=sys.stderr)
    L = []
    L.append('T93 sites.py -- rule E at every select site, own model vs OR-join vs plain shortest path (ps, raw, no guard)')
    L.append('own = earliest req rise (AND/C wait for last input) - latest select change, common launch <link>.ctl.u.u')
    L.append('OR = C-elements crossed on the req path rise on their FIRST derived input (research semantics); '
             'plain = shortest path ignoring AND taps too')
    L.append('<2^12 = own with select cone restricted to loop counter < 2^12 ("=" when the select cone has no adder)')
    L.append("research raw: its raw margin at ITS launch (nextpnr SDF, a different delay model); in () = that "
             "site gate's research number shown on rows of other launches, for reference")
    L.append('T= links treated as transparent (launch is upstream of them)')
    L.append('')
    key = lambda r: (r['design'], r['site'], r['gate'], not r['research_launch'], r['how'], r['launch'],
                     r['transparent'], CORNERS.index(r['corner']))
    for r in sorted(rows, key=key):
        L.append(fmt_row(r))
    L.append('')
    L.append('== SUMMARY ==')
    slines, neg_own, or_only, both, rneg, gcls = summarise(rows)
    L += slines
    L.append('')
    L.append(f'sites checked: {len({(r["design"], r["site"]) for r in rows})} '
             f'({len({(r["design"], r["gate"]) for r in rows})} gates), rows: {len(rows)} '
             f'({sum("own" in r for r in rows)} with a result)')
    L.append(f'own-model negative at either corner (any launch): {len(neg_own)}')
    for des, site, ow, of, b in neg_own:
        L.append(f'  {des} {site}: worst {ow}, fastmin {of}  (binding: {b})')
    L.append(f'research-flagged sites (raw < 0 or guarded VIOLATED): {len(rneg)}: ' + ', '.join(f'{d} {s}' for d, s in rneg))
    L.append(f'  negative under OR-join at the research launch but own >= 0 everywhere ("OR-join only"): {len(or_only)}: '
             + ', '.join(f'{d} {s}' for d, s in or_only))
    L.append(f'  negative under both own and OR-join: {len(both)}: ' + ', '.join(f'{d} {s}' for d, s in both))
    rest = [x for x in rneg if x not in or_only and x not in both]
    L.append(f'  OR-join >= 0 and own >= 0 (research flag from its guardband / SDF only): {len(rest)}: '
             + ', '.join(f'{d} {s}' for d, s in rest))
    L.append("guarded view (research's guard on our numbers, research launch, either corner):")
    for k, v in sorted(gcls.items()):
        L.append(f'  {k}: {len(v)}: ' + ', '.join(v))
    L.append('')
    L.append('== SANITY: ucond_br6 rows vs results.txt (rule_e.py) ==')
    sl, sok = sanity_br6(rows)
    L += sl
    LEGACY_ENG.clear()
    L.append(f'  -> {"all equal to results.txt (transparent rows: in latches-only mode; the default adds the transparent link en path)" if sok else "MISMATCH"}')
    if not a.no_plant:
        L.append('')
        L.append('== SANITY: planted delay on other sites (copy of netlist_baked.v, full re-parse) ==')
        L += plant_test()
    if notes:
        L.append('')
        L.append('== NOTES (pin mapping, launch discovery) ==')
        L += ['  ' + n for n in dict.fromkeys(notes)]
    open(os.path.join(H, 'sites_results.txt'), 'w').write('\n'.join(L) + '\n')
    json.dump(dict(rows=rows, notes=notes), open(os.path.join(H, 'sites_results.json'), 'w'), indent=1, default=str)
    print('\n'.join(L))


if __name__ == '__main__':
    main()
