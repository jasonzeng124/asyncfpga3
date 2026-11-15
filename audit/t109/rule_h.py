#!/usr/bin/env python3
"""T109 (audit, own code): rule H (hold: every latch bit closes before the data its own release lets in can arrive),
computed on the BAKED gate-level netlist of one GLS corner (netlist_baked.v: the delays the simulator runs), with the
audit's own graph (t93/sta_lib.py).  usage: rule_h.py WORKDIR ROUTED_JSON [LINK_REGEX]

Per latch instance L (bd_link / pipe stage; LUT latches found as in t104/mon_latch1.py):
  start   = the net driving L's enable pins (its controller node, at its driver);
  t_close = max over L's latch LUTs of (ICBUF start->en pin + LUT arc en->O): the last bit to close;
  t_dist  = shortest path from start to any D pin of L, through EVERY cell (state nodes fire the moment an input
            reaches them = OR-join lower bound, the same bound research's earliest_disturbance uses), not through L's
            own latch LUTs;
  margin  = t_dist - t_close (no guard).  The path behind t_dist is printed with each state node it crosses, so a
  negative row can be checked: does each crossed state node really fire on THAT input, or does it wait for another?"""
import sys, os, re, json, heapq, collections
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(H, '..', 't93'))
import sta_lib as S
W, RJ = sys.argv[1:3]; rx = re.compile(sys.argv[3] if len(sys.argv) > 3 else ".")
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
ic_src = {o: i for (i, o, d) in N.ic.values()}
ic_d = {o: d for (i, o, d) in N.ic.values()}
logical = {}   # c_ cell -> routed-json cell name(s)
for cn, c in m["cells"].items():
    bel = c["attributes"].get("NEXTPNR_BEL")
    if bel:
        site = bel  # names.map maps site strings like 'SLICE_X..Y../A6LUT'
        if site in c_of_site: logical.setdefault(c_of_site[site], []).append(cn)
luts = collections.defaultdict(list)
for cn, c in m["cells"].items():
    mm = re.match(r'(bridge_i\.udut\..*)\.lat\.(pair\[\d+\]|odd)\.u(\$LUT6|\$LUT5)?$', cn)
    if not mm: continue
    cc = c["connections"]; dirs = c.get("port_directions", {})
    ins = {b for p, bb in cc.items() if dirs.get(p) == "input" for b in bb if isinstance(b, int)}
    outs = {b for p, bb in cc.items() if dirs.get(p) == "output" for b in bb if isinstance(b, int)}
    luts[mm[1]].append((c["attributes"].get("NEXTPNR_BEL"), ins, outs))
rows = []; JS = []
for inst, lst in sorted(luts.items()):
    if not rx.search(inst): continue
    allouts = set().union(*(o for _, _, o in lst))
    cand = [ins - allouts - {b for b in ins if any(n.startswith('$PACKER') for n in names_of_bit[b])} for _, ins, _ in lst]
    shared = set.intersection(*cand) if len(cand) > 1 else set()
    if len(cand) == 1:
        enc = [b for b in cand[0] if any(re.search(r'(_ack|_req|_rack|\.c|\.a\[\d+\])$', n) for n in names_of_bit[b])]
        shared = set(enc) if len(enc) == 1 else set()
    if len(shared) != 1: rows.append((inst, 'UNMAPPED')); continue
    en_b = shared.pop(); en_w = wire_of_bit(en_b)
    cells, dpins, t_close, worst_bit = set(), set(), -1, None
    for (bel, ins, outs), cs in zip(lst, cand):
        c = c_of_site.get(bel)
        if c is None or c not in N.cells: continue
        cells.add(c); pins = N.cells[c]['pins']; out = N.cells[c]['out']
        d_ws = {wire_of_bit(b) for b in cs - {en_b}}
        for p, w in pins.items():
            if not p.startswith('A'): continue
            src = ic_src.get(w)
            if src == en_w:
                t = ic_d[w] + N.cells[c]['params'].get(f'T{p}{out}', 124)
                if t > t_close: t_close, worst_bit = t, c
            elif src in d_ws:
                dpins.add(w)
    own_out = {N.cells[c]['pins'][N.cells[c]['out']] for c in cells}
    # Dijkstra from en_w (OR-join through every cell), not through own latch outputs
    best = {en_w: 0}; prev = {}; hq = [(0, en_w)]; hit = None
    while hq:
        t, net = heapq.heappop(hq)
        if t > best.get(net, 1e18): continue
        if net in dpins: hit = (t, net); break
        for (src, dst, d, kind, cell, pin) in N.fan.get(net, ()):
            if dst in own_out: continue
            if t + d < best.get(dst, 1e18):
                best[dst] = t + d; prev[dst] = (net, kind, cell, pin, d); heapq.heappush(hq, (t + d, dst))
    if hit is None: rows.append((inst, 'NO PATH', t_close)); continue
    path = []; n = hit[1]
    while n in prev:
        src, kind, cell, pin, d = prev[n]
        st = 'STATE ' if (kind == 'lut' and n in N.state_nets) else ''
        path.append(f"{best[n]:6d} {st}{kind}:{cell}.{pin} -> {name_of_wire.get(n, n)} [{'|'.join(logical.get(cell, [''])) if kind == 'lut' else ''}]")
        n = src
    # first state node the path crosses, and the pin it enters by (for the dynamic which-input-was-last check)
    chain = []; n = hit[1]
    while n in prev:
        src, kind, cell, pin, d = prev[n]; chain.append((n, kind, cell, pin)); n = src
    first = next(((cell, pin, N.cells[cell]['pins'][pin]) for (n2, kind, cell, pin) in reversed(chain)
                  if kind == 'lut' and n2 in N.state_nets), None)
    lat = [(c, [p for p, w in N.cells[c]['pins'].items() if p.startswith('A') and ic_src.get(w) == en_w][0],
            [p for p, w in N.cells[c]['pins'].items() if w in dpins]) for c in sorted(cells)]
    JS.append(dict(inst=inst, start=en_w, margin=hit[0] - t_close, close=t_close, disturb=hit[0], latches=lat,
                   first_state=first and dict(cell=first[0], entry=first[1],
                        inputs=sorted(p for p in N.cells[first[0]]['support'] and [f'A{k}' for k in N.cells[first[0]]['support']] if p in N.cells[first[0]]['pins'] and int(p[1]) not in N.fb_pins.get(first[0], set())),
                        logical=logical.get(first[0]))))
    rows.append((inst, hit[0] - t_close, t_close, hit[0], name_of_wire.get(en_w, en_w), list(reversed(path))))
for r in sorted(rows, key=lambda r: r[1] if isinstance(r[1], int) else 1e9):
    if not isinstance(r[1], int): print(f"{r[0]:60s} {r[1:]}"); continue
    print(f"{r[0]:60s} margin {r[1]:6d}  close {r[2]:5d}  disturb {r[3]:5d}  start {r[4]}")
    if os.environ.get('PATHS') and (r[1] < int(os.environ.get('PATHS'))):
        for p in r[5]: print('      ' + p)
if os.environ.get('JSON'): json.dump(JS, open(os.environ['JSON'], 'w'), indent=1)
