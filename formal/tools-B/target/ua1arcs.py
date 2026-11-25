#!/usr/bin/env python3
"""Shard B: generate the ua1Path/ua1Loop arc lists of Formal/Cells/Ua1Static.lean from lean2json output and a
baseline dump (vector (12,18), corner 0.5): ua1's feedback loop, and the causal back-trace of the g-pin fall
that ends ua1's tightest episode (601880 ps) to ua1's own rise (600888 ps).
usage: ua1arcs.py NET.json DUMP.json"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.argv = [sys.argv[0], sys.argv[1], sys.argv[2], "0.5", "1.0"]
src = open(os.path.join(HERE, "kstar.py")).read(); src = src[:src.index("res = []")]
ns = {}; exec(compile(src, "kstar.py", "exec"), ns)
g, crit = ns["g"], ns["crit"]
gi = next(i for i, G in enumerate(g) if G["name"] == "SLICE_X2Y18.DLUT.O6"); G = g[gi]
n = G["ins"][0]; route = []
while g[n]["k"] == 1 and n != gi: route.append(n); n = g[n]["ins"][0]
loop = [(m, 0) for m in route] + [(gi, 0)]
arcs, ok = crit(G["ins"][4], 601880, 600888 - 5000, gi); assert ok
path = arcs + [(gi, 4)]
fmt = lambda l: "[" + ", ".join("⟨%d, %d, %d, %d⟩" % tuple(g[m]["arcs"][p][k] for k in ("fmin", "fmax", "smin", "smax")) for m, p in l) + "]"
print("def ua1Path : List Arc := " + fmt(path)); print("def ua1Loop : List Arc := " + fmt(loop))
