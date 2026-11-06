#!/usr/bin/env python3
"""Shard B (UNTRUSTED helper): the ALL-PATHS race table of a decoded netlist.
For every storage gate q (k >= 2, one pin j whose copy-chain source is q's own output) and every other pin i,
the shortest graph distance from q's output node to q's pin i (sum of arc FAST_MIN, resp. SLOW_MIN, over every
gate pin the path enters, pin i's own arc included), against the loop's longest delay (pin j's arc + its copy
chain, FAST_MAX resp. SLOW_MAX). Only RACE-RELEVANT pins of q are path ends (see relevant()). Pins outside a gate's INIT support carry no change and are skipped. This bounds EVERY path, not only the simulated episodes of racetab.py.
Corner-uniform threshold per (q, i): kappa* = min over c in {0,1} of (D_c - L_c) / (D_c + L_c) (g = 1); exact for
each path at both ends of the corner range, so for every corner (linear in c).
With --cut, paths may not pass through another storage gate (comb-only return paths: what remains if every
intermediate storage node is assumed opaque, i.e. a path through it counts as that node's own switch event).
usage: allpaths.py NET.json ARBS.json OUT.json [prune_factor] [--cut]"""
import json, sys, heapq
CUT = "--cut" in sys.argv; av = [a for a in sys.argv if a != "--cut"]
NETF, ARBF, OUTF = av[1:4]; PF = float(av[4]) if len(av) > 4 else 3.0
N = json.load(open(NETF)); g = N["gates"]; nn = len(N["nodes"])
arbq = {a["qi"] for a in json.load(open(ARBF))}
drv = {G["out"]: gi for gi, G in enumerate(g)}
def dep(G, p):
    # pin p is in the INIT support of G (some address pair differing only in bit p differs in output)
    k, I = G["k"], G["init"]
    return any(((I >> a) & 1) != ((I >> (a | (1 << p))) & 1) for a in range(1 << k) if not a >> p & 1)
fan = [[] for _ in range(nn)]   # node -> [(gate, pin)], support pins only (others cannot carry a change)
for gi, G in enumerate(g):
    for p, m in enumerate(G["ins"]):
        if dep(G, p): fan[m].append((gi, p))
def fbpin(gi):
    G = g[gi]
    for j, n in enumerate(G["ins"]):
        m, ch = n, []
        while m in drv and g[drv[m]]["k"] == 1 and g[drv[m]]["init"] == 2 and m != G["out"] and len(ch) < 80:
            ch.append(drv[m]); m = g[drv[m]]["ins"][0]
        if m == G["out"]: return j, ch
    return None, None
def bit(G, a): return (G["init"] >> a) & 1
def relevant(G, j, i):
    """pin i is RACE-RELEVANT for storage gate G with feedback pin j: from some forcing address (output the same b
    for both feedback values) flipping pin i reaches a HOLD address (output = feedback value, b confirmed only
    through the loop). Changes of an irrelevant pin take a forced output to another forced output (combinational
    following, no loop race) or start from a non-forced state."""
    k = G["k"]
    for a in range(1 << k):
        if a >> j & 1: continue
        b0, b1 = bit(G, a), bit(G, a | 1 << j)
        if b0 != b1: continue
        a2 = a ^ (1 << i); c0, c1 = bit(G, a2 & ~(1 << j)), bit(G, a2 | 1 << j)
        if c0 == 0 and c1 == 1: return True
    return False
def dij(src, key, limit, target_gate):
    # distances to each pin of target_gate; paths start at node src, edge (m -> g.out) via pin p costs arc[key]
    dist = {src: 0}; pq = [(0, src)]; best = {}
    while pq:
        d, m = heapq.heappop(pq)
        if d > dist.get(m, 1 << 60) or d > limit: continue
        for gi, p in fan[m]:
            nd = d + g[gi]["arcs"][p][key]
            if gi == target_gate:
                if nd < best.get(p, 1 << 60): best[p] = nd
                continue          # do not walk through q itself
            if CUT and gi in storage: continue
            o = g[gi]["out"]
            if nd < dist.get(o, 1 << 60) and nd <= limit: dist[o] = nd; heapq.heappush(pq, (nd, o))
    return best
storage = {gi for gi, G in enumerate(g) if G["k"] >= 2 and fbpin(gi)[0] is not None}
print("storage gates", len(storage))
rows = []
for gi, G in enumerate(g):
    if G["k"] < 2: continue
    j, ch = fbpin(gi)
    if j is None: continue
    loop = [(gi, j)] + [(c, 0) for c in ch]
    LF = sum(g[a]["arcs"][p]["fmax"] for a, p in loop); LS = sum(g[a]["arcs"][p]["smax"] for a, p in loop)
    bf = dij(G["out"], "fmin", PF * LF + 1, gi); bs = dij(G["out"], "smin", PF * LS + 1, gi)
    for i in range(G["k"]):
        if i == j or not dep(G, i) or not relevant(G, j, i): continue
        DF = bf.get(i); DS = bs.get(i)
        if DF is None and DS is None: continue
        DF = DF if DF is not None else 10**9; DS = DS if DS is not None else 10**9
        k = min((DF - LF) / (DF + LF), (DS - LS) / (DS + LS))
        rows.append(dict(q=gi, name=G["name"], arb=gi in arbq, pin=i, fbpin=j, LF=LF, LS=LS, DF=DF, DS=DS, kstar=k))
rows.sort(key=lambda r: r["kstar"])
json.dump(rows, open(OUTF, "w"))
nst = len({r["q"] for r in rows})
print("storage gates with a short return path:", nst, "rows", len(rows))
for r in rows[:40]: print("%7d %-40s arb=%d pin %d fb %d  L=%d/%d  D=%d/%d  k*=%.3f" % (r["q"], r["name"][:40], r["arb"], r["pin"], r["fbpin"], r["LF"], r["LS"], r["DF"], r["DS"], r["kstar"]))
