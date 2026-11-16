#!/usr/bin/env python3
"""T127 (audit, own code): controller self-feedback race (formal C13), static, on the BAKED netlist of one own GLS corner.
For the LUT state node whose routed-json cell name matches CELL_REGEX: its output net o;
  fb  = min over its feedback pins k of (ICBUF o -> pin k + LUT arc A_k -> O)   (its own new state must arrive first)
  B_p = earliest arrival (OR-join through every OTHER cell) from o back to its non-feedback input pin p + LUT arc A_p -> O
  slack_p = B_p - max over fb pins of the feedback arrival (latest own-state arrival, the conservative side)
usage: fb.py WORKDIR ROUTED_JSON CELL_REGEX"""
import sys, os, re, json, heapq
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(H, '..', 't93'))
import sta_lib as S
W, RJ, RX = sys.argv[1:4]
N = S.Netlist(os.path.join(W, 'netlist_baked.v'))
m = list(json.load(open(RJ))["modules"].values())[0]
site_of_c, c_of_site = S.read_names_map(os.path.join(W, 'names.map'))
wire_of_name, name_of_wire = S.read_nets_map(os.path.join(W, 'nets.map'))
ic_by_out = {o: (i, d) for (i, o, d) in N.ic.values()}
for cn, c in m["cells"].items():
    if not re.search(RX, cn): continue
    cc = c_of_site.get(c["attributes"].get("NEXTPNR_BEL"))
    if cc is None or cc not in N.cells: print(cn, 'unmapped'); continue
    C = N.cells[cc]; out = C['out']; o = C['pins'][out]; fb = C.get('fb', set())
    if not fb: print(cn, cc, 'no feedback pin'); continue
    arr = {}
    for k in sorted(C['support']):
        p = f'A{k}'; net = C['pins'].get(p)
        if net is None: continue
        arc = C['params'].get(f'TA{k}{out}', 124)
        if k in fb:
            i, d = ic_by_out.get(net, (None, None)); arr[p] = ('fb', (d if i == o else None), arc); continue
        best = {o: 0}; hq = [(0, o)]; got = None
        while hq:
            t, n = heapq.heappop(hq)
            if t > best.get(n, 1e18): continue
            if n == net: got = t; break
            for (src, dst, d, kind, cell, pin) in N.fan.get(n, ()):
                if cell == cc: continue
                if t + d < best.get(dst, 1e18): best[dst] = t + d; heapq.heappush(hq, (t + d, dst))
        arr[p] = ('in', got, arc)
    fbt = [v[1] + v[2] for v in arr.values() if v[0] == 'fb' and v[1] is not None]
    fmax = max(fbt) if fbt else None
    print(f"{cn} ({cc}, out {out}): feedback pins {sorted(fb)}  feedback arrival at O: {fbt}")
    for p, (kind, t, arc) in sorted(arr.items()):
        if kind == 'in':
            print(f"   {p} {name_of_wire.get(C['pins'][p], C['pins'][p])}: return path {t} + arc {arc} = {None if t is None else t + arc}"
                  f"  slack vs feedback {None if (t is None or fmax is None) else t + arc - fmax}")
