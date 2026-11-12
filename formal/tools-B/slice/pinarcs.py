#!/usr/bin/env python3
"""[slice diag] per-arc delays of the composite route of pin (reader v, source w) in the collapsed cone (as build.py),
and need(c1,c2) = hiC(c2)(v,b) - loC(c1)(v,a) for a TO row. usage: pinarcs.py v a b sep"""
import json, sys, math
from fractions import Fraction as F
net = json.load(open("/tmp/claude-0/slice/base/net.json")); names = net["nodes"]; G = net["gates"]
idx = {n: i for i, n in enumerate(names)}; BJ = json.load(open("/tmp/claude-0/slice/base/bnd.json")); ENV = set(idx[x] for x in BJ["env"])
drv = {g["out"]: gi for gi, g in enumerate(G) if g["out"] not in ENV}
def is_copy(g): return g["k"] == 1 and g["init"] == 2
def chain(u):
    arcs = []
    while u in drv and is_copy(G[drv[u]]):
        g = G[drv[u]]; arcs.append(g["arcs"][0]); u = g["ins"][0]
    return u, arcs
def pin(v, w):
    g = G[drv[idx[v]]]
    for j, u in enumerate(g["ins"]):
        s, carcs = chain(u)
        if s == idx[w]: return [g["arcs"][j]] + carcs
def lerp(x, y, c): return (1 - c) * x + c * y
v, a, b, sep = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
A = pin(v, a); B = pin(v, b); print("arcs (v,a):", A); print("arcs (v,b):", B)
lo = lambda c: sum(math.ceil(lerp(x["fmin"], x["smin"], c)) for x in A)
hi = lambda c: sum(math.floor(lerp(x["fmax"], x["smax"], c)) for x in B)
for k in (1, 2, 4, 8, 12, 16):
    print("K=%2d needs:" % k, [hi(F(i + 1, k)) - lo(F(i, k)) for i in range(k)], "Sep", sep)
for c1 in [F(i, 20) for i in range(21)]:
    c2 = c1; step = F(1, 1000)
    while c2 + step <= 1 and hi(c2 + step) - lo(c1) <= sep: c2 += step
    print("c1=%.2f: widest c2 with need <= Sep: %.3f (width %.3f)" % (c1, c2, c2 - c1))
