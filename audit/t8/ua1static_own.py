#!/usr/bin/env python3
"""ua1static_own.py (audit T8): B's Ua1Static arc lists checked against the auditor's own decoded net.

    python3 -I ua1static_own.py NET.json

(1) ua1 = gate SLICE_X2Y18.DLUT.O6. Loop: from its input 0 follow 1-input gates back to ua1 (own walk); compare the
    arc list with B's ua1Loop. (2) Path: search my net for a chain of 17 (gate, pin) arcs from ua1's output to ua1
    pin A5 (input 4) whose arcs equal B's ua1Path in order (backward DFS, arcs must match exactly). (3) Recompute
    pathLo / loopHi with exact rationals (Spec Adm: [max(fmin/g, (1-k)lerp(fmin,smin,c)), min(smax*g, (1+k)lerp(fmax,smax,c))],
    integer delays: ceil / floor) at g = 1, c = 1/2, k in 0.15, 0.155, 0.16.
"""
import json, sys, math
from fractions import Fraction as Fr

PATH = [(0,0,0,0),(38,47,114,138),(33,60,111,153),(0,0,0,0),(0,0,0,0),(83,104,202,250),(0,0,0,0),(38,47,114,138),
        (34,51,103,133),(0,0,0,0),(0,0,0,0),(217,270,516,640),(0,0,0,0),(38,47,114,138),(0,0,0,0),(0,0,0,0),(78,98,191,237)]
LOOP = [(0,0,0,0),(38,47,114,138),(36,53,103,133),(33,51,113,147),(0,0,0,0),(0,0,0,0),(219,272,521,646)]

N = json.load(open(sys.argv[1])); G = N["gates"]; names = N["nodes"]
byout = {g["out"]: g for g in G}
arc = lambda g, p: tuple(g["arcs"][p][k] for k in ("fmin", "fmax", "smin", "smax"))
ua1 = next(g for g in G if g["name"] == "SLICE_X2Y18.DLUT.O6")
# (1) loop
loop = []; n = ua1["ins"][0]
while True:
    g = byout[n]
    if g is ua1: break
    assert g["k"] == 1, g["name"]
    loop.append(arc(g, 0)); n = g["ins"][0]
loop = loop + [arc(ua1, 0)]       # B lists the route walking back from ua1's pin, then ua1's own pin-A1 arc
print("loop: %d arcs, equal to B's ua1Loop (B's order: back from the pin): %s" % (len(loop), loop == LOOP))
# (2) path: last arc is ua1 pin 4; search backwards
target = ua1["out"]
sols = []
def dfs(node, i, acc):
    # B lists the back-trace from ua1 pin A5's driver towards ua1's output: PATH[i] for i = 0, 1, ... 15
    if i == len(PATH) - 1:
        if node == target: sols.append(list(reversed(acc)))
        return
    g = byout.get(node)
    if g is None: return
    for p in range(g["k"]):
        if arc(g, p) == PATH[i]:
            dfs(g["ins"][p], i + 1, acc + [(g["name"], p)])
assert arc(ua1, 4) == PATH[-1]
dfs(ua1["ins"][4], 0, [(ua1["name"], 4)])
print("path: %d matching chains from ua1.out to ua1 pin A5" % len(sols))
for s in sols[:3]:
    print("   ", " -> ".join("%s/%d" % x for x in s))
# (3) sums
def lo(e, k, c=Fr(1, 2), g=Fr(1)):
    fmin, fmax, smin, smax = e
    return math.ceil(max((1 - k) * ((1 - c) * fmin + c * smin), Fr(fmin) / g))
def hi(e, k, c=Fr(1, 2), g=Fr(1)):
    fmin, fmax, smin, smax = e
    return math.floor(min((1 + k) * ((1 - c) * fmax + c * smax), Fr(smax) * g))
for k in (Fr(15, 100), Fr(155, 1000), Fr(16, 100)):
    pl = sum(lo(e, k) for e in PATH); lh = sum(hi(e, k) for e in LOOP)
    print("kappa %s: pathLo %d loopHi %d  -> %s" % (float(k), pl, lh, "holds (loop <= path)" if lh <= pl else "FAILS (path < loop)"))
