#!/usr/bin/env python3
"""Shard B (UNTRUSTED): static race bound for shard C's persistence pairs (node n, re-enabler m). Assumption: m's
return is a consequence of the change of the C input k that completed n's excitation (k ranges over n's other C inputs;
the worst k is reported). The excitation, as read by n, lasts at least
   (1-κ)·[Dmin(src_k -> src_m) + lo(m pin)] - (1+κ)·hi(k pin)
and n switches cleanly if that is >= (1+κ)·hi(loop). κ* = largest κ (corner-uniform, g = 1) for which this holds at both
corner ends. usage: persist_static.py NET.json CELEM.json PAIRS.txt"""
import json, sys, heapq
N = json.load(open(sys.argv[1])); g = N["gates"]
C = json.load(open(sys.argv[2])); C = C["rows"] if isinstance(C, dict) else C
byname = {r["name"]: r for r in C}
def dep(G, p):
    k, I = G["k"], G["init"]
    return any(((I >> a) & 1) != ((I >> (a | (1 << p))) & 1) for a in range(1 << k) if not a >> p & 1)
fan = [[] for _ in N["nodes"]]
for gi, G in enumerate(g):
    for p, m in enumerate(G["ins"]):
        if dep(G, p): fan[m].append((gi, p))
def dist(src, dst, key):
    d0 = {src: 0}; pq = [(0, src)]
    while pq:
        d, m = heapq.heappop(pq)
        if m == dst: return d
        if d > d0[m]: continue
        for gi, p in fan[m]:
            o = g[gi]["out"]; nd = d + g[gi]["arcs"][p][key]
            if nd < d0.get(o, 1 << 60): d0[o] = nd; heapq.heappush(pq, (nd, o))
def comp(r, i, key): return g[r["q"]]["arcs"][i][key] + sum(g[x]["arcs"][0][key] for x in r["chains"][i])
for line in open(sys.argv[3]):
    cnt, a, _, b = line.split()
    sl, lut = a.split("."); r = byname["%s.%sLUT.O6" % (sl, lut[0])]
    sl2, lut2 = b.split("."); mname = "%s.%sLUT.O6" % (sl2, lut2[0])
    mi = [i for i in r["ci"] if g[r["srcs"][i]]["name"] == mname] if True else []
    if not mi: print(a, b, "re-enabler is not a direct C-input source"); continue
    m = mi[0]; worst = None
    for k in r["ci"]:
        if k == m: continue
        res = []
        for kmin, kmax in [("fmin", "fmax"), ("smin", "smax")]:
            D = dist(r["srcs"][k], r["srcs"][m], kmin)
            if D is None: res = None; break
            res.append((D + comp(r, m, kmin), comp(r, k, kmax) + comp(r, r["fb"], kmax)))
        if res is None: ks = 9.9
        else: ks = min((A - B) / (A + B) for A, B in res)
        if worst is None or ks < worst[0]: worst = (ks, k, res)
    print("%-18s by %-16s walks %3s: kappa* %s (completing input pin %s; [return, excitation+loop] fast/slow %s)" % (
        a, b, cnt, "%.3f" % worst[0] if worst[0] < 9 else "no path", worst[1], worst[2]))
