#!/usr/bin/env python3
"""T128 (audit, own code): static bundling (rule A style) check of one fused op, on the BAKED netlist of one own GLS corner.
For each upstream link U (its controller/enable node en_U) and each bit b of the downstream latch D_link:
  data_max(U,b) = LONGEST path en_U -> U's latch LUT (en->O arc) -> combinational cone (no other state node) -> b's D pin
                  + b's D->O arc                       (latest the new operand can reach b's output)
  req_min(U,b)  = SHORTEST path en_U -> ... -> b's enable pin (OR-join through every cell, incl. the request join, the
                  delay line, the steer and the downstream controller) + b's en->O arc  (earliest b can close)
  slack = req_min - data_max (must be > 0: b closes only after the operand has arrived).
OR-join on the request side is conservative (the request join is a C-element that waits for its last input).
usage: bundle.py WORKDIR ROUTED_JSON DOWN_REGEX UP_REGEX"""
import sys, os, re, json, heapq, collections
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(H, '..', 't93'))
import sta_lib as S
sys.setrecursionlimit(100000)
W, RJ, DRX, URX = sys.argv[1:5]
N = S.Netlist(os.path.join(W, 'netlist_baked.v'))
m = list(json.load(open(RJ))["modules"].values())[0]
site_of_c, c_of_site = S.read_names_map(os.path.join(W, 'names.map'))
wire_of_name, name_of_wire = S.read_nets_map(os.path.join(W, 'nets.map'))
names_of_bit = collections.defaultdict(set)
for n, v in m["netnames"].items():
    for b in v["bits"]: names_of_bit[b].add(n)
def wire_of_bit(b):
    for n in names_of_bit[b]:
        if n in wire_of_name: return wire_of_name[n]
ic_src = {o: i for (i, o, d) in N.ic.values()}; ic_d = {o: d for (i, o, d) in N.ic.values()}
luts = collections.defaultdict(list)
for cn, c in m["cells"].items():
    mm = re.match(r'(bridge_i\.udut\..*)\.lat\.(pair\[\d+\]|odd)\.u(\$LUT6|\$LUT5)?$', cn)
    if not mm: continue
    cc = c["connections"]; dirs = c.get("port_directions", {})
    ins = {b for p, bb in cc.items() if dirs.get(p) == "input" for b in bb if isinstance(b, int)}
    outs = {b for p, bb in cc.items() if dirs.get(p) == "output" for b in bb if isinstance(b, int)}
    luts[mm[1]].append((cn, c["attributes"].get("NEXTPNR_BEL"), ins, outs))
def link(inst):
    lst = luts[inst]; allouts = set().union(*(o for _, _, _, o in lst))
    cand = [ins - allouts - {b for b in ins if any(n.startswith('$PACKER') for n in names_of_bit[b])} for _, _, ins, _ in lst]
    shared = set.intersection(*cand) if len(cand) > 1 else set()
    if len(cand) == 1:
        enc = [b for b in cand[0] if any(re.search(r'(_ack|_req|_rack|\.c|\.a\[\d+\])$', n) for n in names_of_bit[b])]
        shared = set(enc) if len(enc) == 1 else set()
    if len(shared) != 1: return None
    en_b = shared.pop(); en_w = wire_of_bit(en_b); bits = []
    for (cn, bel, ins, outs), cs in zip(lst, cand):
        c = c_of_site.get(bel)
        if c is None or c not in N.cells: continue
        C = N.cells[c]; out = C['out']; enp = None; dps = []
        d_ws = {wire_of_bit(b) for b in cs - {en_b}}
        for p, w in C['pins'].items():
            if not p.startswith('A'): continue
            if ic_src.get(w) == en_w: enp = p
            elif ic_src.get(w) in d_ws: dps.append(p)
        bits.append(dict(name=cn, cell=c, out=out, enp=enp, dps=dps))
    return en_w, bits
# delay-chain gate inputs (bd_delay_gated: g[k] = s[k] & gate, k >= 1): a RISING request ripples through s[k] only, so the
# request search may enter g[k] (k >= 1) only from g[k-1]'s output (the gate is a fast-FALL path).
logical = {}
for cn, c in m["cells"].items():
    cc_ = c_of_site.get(c["attributes"].get("NEXTPNR_BEL"))
    if cc_: logical.setdefault(cc_, []).append(cn)
chain_prev = {}   # c_ cell of g[k] (k>=1) -> output net of g[k-1]
by_name = {n: c for c, ns in logical.items() for n in ns}
for c, ns in logical.items():
    for n in ns:
        mm = re.match(r'(.*\.chain\.g)\[(\d+)\]\.u$', n)
        if mm and int(mm[2]) >= 1:
            pc = by_name.get(f"{mm[1]}[{int(mm[2]) - 1}].u")
            if pc in N.cells: chain_prev[c] = N.cells[pc]['pins'][N.cells[pc]['out']]
def gate_edge(src, cell):
    pv = chain_prev.get(cell)
    return pv is not None and ic_src.get(src, src) != pv and src != pv
downs = [i for i in luts if re.search(DRX, i)]; ups = [i for i in luts if re.search(URX, i)]
assert len(downs) == 1, downs
den, dbits = link(downs[0])
targets = {}   # D-pin net -> list of (bit name, D->O arc)
for b in dbits:
    C = N.cells[b['cell']]
    for p in b['dps']: targets.setdefault(C['pins'][p], []).append((b['name'], C['params'].get(f'T{p}{b["out"]}', 124)))
memo = {}
def longest(net, stack):
    """longest delay from net to each target bit: dict bit -> delay"""
    if net in memo: return memo[net]
    res = {}
    for bn, arc in targets.get(net, ()): res[bn] = max(res.get(bn, -1), arc)
    if net in stack: return res
    stack.add(net)
    for (src, dst, d, kind, cell, pin) in N.fan.get(net, ()):
        if dst in N.state_nets: continue          # stop at other state nodes (latches, C-elements)
        for bn, t in longest(dst, stack).items():
            if d + t > res.get(bn, -1): res[bn] = d + t
    stack.discard(net); memo[net] = res; return res
print(f"downstream {downs[0]} ({len(dbits)} bits, en {name_of_wire.get(den, den)})")
worst = []
for u in sorted(ups):
    L = link(u)
    if L is None: print(u, 'UNMAPPED'); continue
    uen, ubits = L
    # data launch: en_U -> each U latch bit's en pin -> O, then the cone
    dmax = {}
    for b in ubits:
        C = N.cells[b['cell']]; o = C['pins'][b['out']]
        t0 = ic_d[C['pins'][b['enp']]] + C['params'].get(f'T{b["enp"]}{b["out"]}', 124)
        for bn, t in longest(o, set()).items():
            if t0 + t > dmax.get(bn, -1): dmax[bn] = t0 + t
    # request: shortest from en_U to every net
    best = {uen: 0}; hq = [(0, uen)]
    while hq:
        t, n = heapq.heappop(hq)
        if t > best.get(n, 1e18): continue
        for (src, dst, d, kind, cell, pin) in N.fan.get(n, ()):
            if kind == 'lut' and gate_edge(src, cell): continue
            if t + d < best.get(dst, 1e18): best[dst] = t + d; heapq.heappush(hq, (t + d, dst))
    rows = []
    for b in dbits:
        if b['name'] not in dmax: continue
        C = N.cells[b['cell']]; ep = C['pins'][b['enp']]
        if ep not in best: continue
        rq = best[ep] + C['params'].get(f'T{b["enp"]}{b["out"]}', 124)
        rows.append((rq - dmax[b['name']], b['name'], rq, dmax[b['name']]))
    rows.sort()
    if rows:
        print(f"  from {u}: bits reached {len(rows)}; min slack {rows[0][0]} ps at {rows[0][1].split('.')[-2]} (req {rows[0][2]}, data {rows[0][3]})")
        worst.append(rows[0][0])
    else:
        print(f"  from {u}: no bit of the downstream latch reached by both paths")
print(f"chain gate edges excluded on the request side: {len(chain_prev)} chain elements")
print(f"overall min slack: {min(worst) if worst else None}")
