#!/usr/bin/env python3
"""margin/rank.py (shard C, UNTRUSTED): order races.py's candidates by a dynamic estimate from reference runs.

    python3 rank.py NET.json RACES.json K0 OUT.json DUMP.json [DUMP.json ...]

Each DUMP is simadv.py --dump of a reference run (every arc at the fast end (1-K0) FAST_MIN, corner 0; one per
pair). For candidate (q, pin i), every arrival of a change at q's pin i after reset (the flip of the node read by
pin i plus q's pin-i arc) is compared with the nearest LATER arrival at any other support pin j of q. Slowing pin
i's whole route (q's arc + chain hops) from (1-k) FAST_MIN to (1+k) FAST_MAX adds
    extra(k) = (1+k) Lmax - (1-k) Lmin
so the two arrivals swap order once extra(k) > gap, i.e. k > (gap + Lmin - Lmax)/(Lmax + Lmin) =: kre.
kre (min over the arrivals and over the dumps) is the candidate's rank; a candidate whose q or pin i never
changes after reset in any reference run gets kre = 2 (it is still swept, last). An ESTIMATE only: a reordering
is not a failure, and the other arrivals also move with k.
"""
import json, sys
from bisect import bisect_right
netf, racef, K0, outf = sys.argv[1], sys.argv[2], float(sys.argv[3]), sys.argv[4]
dumps = sys.argv[5:]
net = json.load(open(netf)); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
drv = {g["out"]: gi for gi, g in enumerate(G)}
R = json.load(open(racef))
def dep(g, j):
    k, I = g["k"], g["init"]
    return any(((I >> x) & 1) != ((I >> (x ^ (1 << j))) & 1) for x in range(1 << k))
D = []
for f in dumps:
    d = json.load(open(f)); D.append(({int(k): v[1] for k, v in d["nodes"].items()}, d["args"]["R"]))
def fdel(e): return -(-((1 - K0) * e["fmin"]) // 1)
for r in R:
    q = idx[r["node"]]; g = G[drv[q]]; i = r["pin"]
    arcs = [(drv[idx[n]], p) for n, p in r["arcs"]]
    Lmax = sum(G[a]["arcs"][p]["fmax"] for a, p in arcs); Lmin = sum(G[a]["arcs"][p]["fmin"] for a, p in arcs)
    best = 2.0; why = None
    for fl, R0 in D:
        ti = [t + fdel(g["arcs"][i]) for t in fl.get(g["ins"][i], []) if t >= R0]
        if not ti or not fl.get(q): continue
        oth = sorted(t + fdel(g["arcs"][j]) for j in range(g["k"]) if j != i and dep(g, j)
                     for t in fl.get(g["ins"][j], []) if t >= R0)
        for t in ti:
            x = bisect_right(oth, t)
            if x == len(oth): continue
            gap = oth[x] - t
            k = (gap + Lmin - Lmax) / (Lmax + Lmin)
            if k < best: best = k; why = (t, gap)
        if best == 2.0: best = 1.5   # active, but no later arrival on another pin
    r["kre"] = round(best, 4); r["kre_at"] = why
R.sort(key=lambda r: r["kre"])
json.dump(R, open(outf, "w"), indent=0)
