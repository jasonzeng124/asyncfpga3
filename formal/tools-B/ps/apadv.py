#!/usr/bin/env python3
"""Shard B (UNTRUSTED): per-pin posmap for simb.py from allpaths.py's shortest static return path of one storage gate:
every arc of the shortest path (q's output -> q's race-relevant pin, FAST_MIN weights) at the fast end (-1), q's
feedback loop at the slow end (2). usage: apadv.py NET.json GATE PIN OUT_posmap.json"""
import json, sys, heapq
N = json.load(open(sys.argv[1])); g = N["gates"]; q = int(sys.argv[2]); pin = int(sys.argv[3])
drv = {G["out"]: i for i, G in enumerate(g)}
def dep(G, p):
    k, I = G["k"], G["init"]
    return any(((I >> a) & 1) != ((I >> (a | (1 << p))) & 1) for a in range(1 << k) if not a >> p & 1)
fan = [[] for _ in N["nodes"]]
for gi, G in enumerate(g):
    for p, m in enumerate(G["ins"]):
        if dep(G, p): fan[m].append((gi, p))
src = g[q]["out"]; dist = {src: 0}; pred = {}; pq = [(0, src)]; best = None
while pq:
    d, m = heapq.heappop(pq)
    if d > dist[m]: continue
    for gi, p in fan[m]:
        nd = d + g[gi]["arcs"][p]["fmin"]
        if gi == q:
            if p == pin and (best is None or nd < best[0]): best = (nd, m)
            continue
        o = g[gi]["out"]
        if nd < dist.get(o, 1 << 60): dist[o] = nd; pred[o] = (m, gi, p); heapq.heappush(pq, (nd, o))
path = [(q, pin)]; m = best[1]
while m != src: a, gi, p = pred[m]; path.append((gi, p)); m = a
loop = []
for j, n in enumerate(g[q]["ins"]):
    m, ch = n, []
    while m in drv and g[drv[m]]["k"] == 1 and m != src and len(ch) < 80: ch.append(drv[m]); m = g[drv[m]]["ins"][0]
    if m == src: loop = [(q, j)] + [(c, 0) for c in ch]; break
pm = {"%d:%d" % (a, p): -1 for a, p in path}; pm.update({"%d:%d" % (a, p): 2 for a, p in loop})
json.dump(pm, open(sys.argv[4], "w"))
print("path arcs", len(path), "fmin", best[0], "loop arcs", len(loop))
