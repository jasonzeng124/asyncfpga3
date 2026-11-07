#!/usr/bin/env python3
"""Shard C (UNTRUSTED, but independent of the simulator's event loop): check a dumped run (simadv --dump) against
Spec's gate relation with fixed per-arc delays: for every gate of the circuit (env nodes' drivers removed), at every
time t >= start, out(t) = INIT bit at the address of in_i(t - d_i), and every d_i is inside Adm(g=1, kappa, corner).
Signals are piecewise constant (v0, flip times). Checks at every breakpoint (input flip + d_i, output flips).
usage: gatecheck.py net.json bnd.json dump.json corner kappa SLOWNODE..."""
import json, sys, math, bisect
from fractions import Fraction as Fr
net = json.load(open(sys.argv[1])); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
BJ = json.load(open(sys.argv[2])); ENV = set(idx[x] for x in BJ["env"])
D = json.load(open(sys.argv[3])); c = Fr(sys.argv[4]); kap = Fr(sys.argv[5]); ARCS = None
if len(sys.argv) > 6 and sys.argv[6].startswith("@"):   # per-arc slow list (simadv --classes JSON, key "S": [[node, pin]])
    ARCS = set((idx[x[0]], x[1]) for x in json.load(open(sys.argv[6][1:]))["S"]); sys.argv = sys.argv[:6]
SLOWN = set(idx[x] for x in sys.argv[6:])
drv = {g["out"]: gi for gi, g in enumerate(G) if g["out"] not in ENV}
# the simulator's slow set (same rule as simadv --slowroutes)
SLOW = set(SLOWN)
for n0 in list(SLOWN):
    gi0 = drv.get(n0)
    for u in G[gi0]["ins"]:
        while u in drv and G[drv[u]]["k"] == 1 and G[drv[u]]["init"] == 2: SLOW.add(u); u = G[drv[u]]["ins"][0]
cs, kf = float(c), float(kap)
EXACT = (kap * 25).denominator == 1 and c == 0
P = int(kap * 25)
def dly(e, slow):
    if EXACT: return ((25 + P) * e["fmax"]) // 25 if slow else ((25 - P) * e["fmin"] + 24) // 25
    lo = (1 - cs) * e["fmin"] + cs * e["smin"]; hi = (1 - cs) * e["fmax"] + cs * e["smax"]
    return int(math.floor(hi * (1 + kf))) if slow else int(math.ceil(lo * (1 - kf)))
def adm(e, d):
    lo = (1 - c) * e["fmin"] + c * e["smin"]; hi = (1 - c) * e["fmax"] + c * e["smax"]
    return (1 - kap) * lo <= d <= (1 + kap) * hi
sig = {int(k): (v[0], v[1]) for k, v in D["nodes"].items()}
def val(n, t):
    v0, fl = sig.get(n, (False, []))
    k = bisect.bisect_right(fl, t)
    return bool(v0) ^ (k % 2 == 1)
tend = D["tend"]; bad = 0; badadm = 0; checked = 0
for o, gi in drv.items():
    g = G[gi]; slow = o in SLOW
    ds = [dly(e, slow if ARCS is None else (o, i) in ARCS) for i, e in enumerate(g["arcs"])]
    for e, d in zip(g["arcs"], ds):
        if not adm(e, d): badadm += 1
    start = max([int(math.ceil((1 + kf) * e["smax"])) for e in g["arcs"]] + [0])
    pts = {start}
    for i, n in enumerate(g["ins"]):
        for t in sig.get(n, (0, []))[1]: pts.add(t + ds[i])
    for t in sig.get(o, (0, []))[1]: pts.add(t)
    for t in sorted(pts):
        if t < start or t > tend: continue
        a = sum((1 << i) for i, n in enumerate(g["ins"]) if val(n, t - ds[i]))
        checked += 1
        if bool((g["init"] >> a) & 1) != val(o, t):
            bad += 1
            if bad <= 5: print("MISMATCH gate", g["name"], "at", t)
print("gates", len(drv), "checks", checked, "mismatches", bad, "arcs outside Adm", badadm, "tend", tend)
