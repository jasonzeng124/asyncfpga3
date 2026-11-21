#!/usr/bin/env python3
"""mux_settle.py DUMPDIR KERNEL_V -- the dynamic counterpart of rule M (corner_audit A'm, 2026-11-16): at every bd_mux,
does the output DATA settle before the output request z_req rises?  Per z_req rise, the last change of any z_data bit
(at its driver, the udat LUT output) before z_req falls; a change after the rise is a token whose request went out
ahead of its data.  Prints per mux: rises, rises with a late data change, the worst lag (ps after z_req rose) and the
smallest lead of the last change before a rise.  Whether a late change is a HAZARD depends on the consumer (a link
latch closes a phase later; a fused cell starts on the request): this measures the race, not the consequence.
(Derived from select_arrival.py, whose header follows.)

select_arrival.py DUMPDIR KERNEL_V -- the select-ARRIVAL race, measured in simulation (PROGRAM "No blanket rules",
2026-11-15 correction after audit T116): a select must not change while the request it gates is high.

  bd_mux   C(x_req, ctl_req . ~s) / C(y_req, ctl_req . s): the window is the mux's output request z_req high (or, when
           the dump has no name for it, the joins' OR `either`, which rises earlier: a stricter window);
  bd_steer req0 = req . ~s, req1 = req . s (combinational): the window is the input req high.
A select bit that changes inside a window can steer the token to the wrong branch, or fire the mux on the wrong input.

DUMPDIR: a fullstack_dump.sh run (nets.map, dump.vcd) -- FAST_MIN and vectors that flip the selects (e.g.
research/data/fifteen/vec_collatz_hold.hex).  KERNEL_V: the route's <kernel>_kernel_bench.v.
Per instance: request rises seen, VIOLATIONS (rises whose window contains a select change), and the smallest lead
(request rise - last select change before it; negative = a change inside the window).
"""
import re, sys, collections, bisect

d, kv = sys.argv[1], sys.argv[2]
src = open(kv).read()
par = {}
def find(x):
    while par.get(x, x) != x:
        par[x] = par.get(par[x], par[x]); x = par[x]
    return x
for a, b in re.findall(r'assign\s+(\w+)\s*=\s*(\w+)\s*;', src):
    par[find(a)] = find(b)
nm = {}
for l in open(d + '/nets.map'):
    if l.startswith('#'): continue
    a, b = l.split()[:2]
    nm.setdefault(b, a)
P = 'bridge_i.udut.'
byclass = collections.defaultdict(list)
for k in list(nm):
    m = re.fullmatch(re.escape(P) + r'(\w+?)(\[(\d+)\])?', k)
    if m: byclass[(find(m.group(1)), m.group(3))].append(k)
def net(expr):
    m = re.fullmatch(r'\s*(\w+)(?:\[(\d+)\])?\s*', expr)
    if not m: return None
    ks = byclass.get((find(m.group(1)), m.group(2))) or (byclass.get((find(m.group(1)), None)) if m.group(2) in (None, '0') else None)
    return nm[ks[0]] if ks else None
insts = []
for m in re.finditer(r'\b(bd_mux|bd_steer)\b\s*(?:#\([^;]*?\))?\s*(\w+)\s*\(([^;]*?)\);', src, re.S):
    kind, name, ports = m.groups()
    pr = dict(re.findall(r'\.(\w+)\(([^()]*)\)', ports))
    s = net(pr.get('s', '')); r = net(pr.get('z_req' if kind == 'bd_mux' else 'req', ''))
    if r is None and kind == 'bd_mux':     # z_req is the end of the mux's delay line, often unnamed in the decoded netlist:
        r = nm.get(P + name + '.either')    # its joins' OR (j0 | j1), the gates the select steers, rises earlier: stricter
    gated = [nm.get(P + name + '.j0'), nm.get(P + name + '.j1')] if kind == 'bd_mux' else \
            [net(pr.get('req0', '')), net(pr.get('req1', ''))]
    if s and r: insts.append((name, kind, s, r, [g for g in gated if g]))
    else: print(f"# {name}: select or request net not in the dump (s={pr.get('s')}, req net missing={r is None})")
# The select AT THE PIN of each gating LUT (after its wire): the decoded netlist models every wire as an ICBUF whose
# output w-net drives the LUT pin (cells/gls/gen.py).  The race is the pin's change, not the driver's (audit T116's
# monitor reads the pin; the driver is earlier by the wire, ~0.5 ns).
nl = open(d + '/netlist.v').read()
icb = {b: a for a, b in re.findall(r'ICBUF \S+ \(\.I\((n\d+)\), \.O\((w\d+)\)\)', nl)}
drv = {}
for mm_ in re.finditer(r"SLICE_LUTX #\(\.INIT\(64'h[0-9a-f]+\)\) \S+ \(([^;]*)\);", nl):
    body = mm_.group(1); pins = dict(re.findall(r'\.(A\d)\((w\d+)\)', body))
    for o_ in re.findall(r'\.O[56]\((n\d+)\)', body):
        drv[o_] = pins
rev = collections.defaultdict(list)
for k_, v_ in nm.items(): rev[v_].append(k_)
def owned(n_, name):                       # a LUT output net that belongs to instance `name` (by any of its names)
    return any(k_.startswith(P + name + '.') for k_ in rev.get(n_, ()))
# z_req when the dump has no name for it: the LUT fed by the last element of the mux's delay line (udly.chain.s[k],
# highest k) whose output carries no name of the mux -- the line's end, i.e. the output request.
for i_, (name, kind, s_, r_, gated) in enumerate(insts):
    if kind != 'bd_mux' or not r_.startswith('n') or not any(k_.endswith('.either') for k_ in rev.get(r_, ())):
        continue
    ch = sorted(((int(m_.group(1)), v_) for k_, v_ in nm.items()
                 for m_ in [re.fullmatch(re.escape(P + name) + r'\.udly\.chain\.s\[(\d+)\]', k_)] if m_), reverse=True)
    if not ch: continue
    last = ch[0][1]
    ends = [o_ for o_, pins in drv.items() if any(icb.get(w) == last for w in pins.values()) and not owned(o_, name)]
    if len(ends) == 1:
        insts[i_] = (name, kind, s_, ends[0], gated)
        print(f"# {name}: z_req = {ends[0]} (end of udly after {P}{name}.udly.chain.s[{ch[0][0]}])")
    else:
        print(f"# {name}: z_req not identified ({len(ends)} candidates); window = the joins' OR")

zbits = {}
for m in re.finditer(r'\bbd_mux\b\s*(?:#\(([^;]*?)\))?\s*(\w+)\s*\(([^;]*?)\);', src, re.S):
    params, name, ports = m.groups()
    pr = dict(re.findall(r'\.(\w+)\(([^()]*)\)', ports))
    w = int((re.search(r'\.W\((\d+)\)', params or '') or [0, 1])[1])
    zd = pr.get('z_data', '').strip()
    bits = [net(f'{zd}[{i}]') for i in range(w)] if w > 1 else [net(zd)]
    zbits[name] = [b for b in bits if b]
    if len(zbits[name]) < w: print(f"# {name}: {w - len(zbits[name])} of {w} z_data bits not in the dump")
muxes = [(name, r_) for name, kind, s_, r_, _ in insts if kind == 'bd_mux']
want = {r for _, r in muxes} | {b for n, _ in muxes for b in zbits.get(n, [])}
ids = collections.defaultdict(list); ev = collections.defaultdict(list); t = 0
for l in open(d + '/dump.vcd'):
    if l.startswith('$var'):
        p = l.split()
        if p[4] in want: ids[p[3]].append(p[4])
    elif l[0] == '#': t = int(l[1:])
    elif l[0] in '01xz':
        for x in ids.get(l[1:].strip(), ()): ev[x].append((t, l[0]))
    elif l[0] == 'b':
        pass
print("instance\trises\tlate_rises\tworst_lag_ps\tmin_lead_ps\tdata_changes")
tot = 0
for name, r in muxes:
    rises = [t for t, v in ev[r] if v == '1']; falls = [t for t, v in ev[r] if v == '0']
    ch = sorted(t for b in zbits.get(name, []) for t, _ in ev[b])
    late = 0; lag = None; lead = None
    for x in rises:
        j = bisect.bisect_right(falls, x); f = falls[j] if j < len(falls) else None
        k = bisect.bisect_right(ch, x)
        inside = [c for c in ch[k:] if f is None or c < f]
        if inside:
            late += 1; g = inside[-1] - x
            if lag is None or g > lag: lag = g
        if k:
            l_ = x - ch[k - 1]
            if lead is None or l_ < lead: lead = l_
    tot += late
    print(f"{name}\t{len(rises)}\t{late}\t{lag if lag is not None else '-'}\t{lead if lead is not None else 'NA'}\t{len(ch)}")
print(f"# rises with a data change after z_req rose: {tot}")
