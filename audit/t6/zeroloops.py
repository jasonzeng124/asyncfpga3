#!/usr/bin/env python3
"""T6: are there cycles made only of zero-delay arcs (any delay assignment inside Adm at kappa<1 gives 0 only
when the Adm interval is [0,0], i.e. fmin = smax = 0 ... we test arcs whose Adm interval CAN be 0: lower end 0)
in the circuit (env-driven gates removed)?  usage: zeroloops.py NET.json BND.json KAPPA CORNER"""
import json, sys, math
from fractions import Fraction as Fr
N = json.load(open(sys.argv[1])); B = json.load(open(sys.argv[2])); k = Fr(sys.argv[3]); c = Fr(sys.argv[4])
idx = {n: i for i, n in enumerate(N["nodes"])}; ENV = set(idx[x] for x in B["env"])
adj = {}
for g in N["gates"]:
    if g["out"] in ENV: continue
    for n, e in zip(g["ins"], g["arcs"]):
        lo = max(Fr(e["fmin"]), (1 - k) * ((1 - c) * e["fmin"] + c * e["smin"]))
        if math.ceil(lo) == 0:
            adj.setdefault(n, []).append(g["out"])
# iterative DFS cycle detection
col = {}; cyc = 0
for s in list(adj):
    if col.get(s): continue
    st = [(s, iter(adj.get(s, ())))]; col[s] = 1
    while st:
        v, it = st[-1]
        for w in it:
            if col.get(w) == 1: cyc += 1; break
            if not col.get(w): col[w] = 1; st.append((w, iter(adj.get(w, ())))); break
        else:
            col[v] = 2; st.pop()
print("zero-capable arcs: %d sources; zero-delay cycles found: %d" % (len(adj), cyc))
