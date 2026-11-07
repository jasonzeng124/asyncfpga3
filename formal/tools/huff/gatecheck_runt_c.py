#!/usr/bin/env python3
"""[Shard C copy, 2026-11-07: adds per-arc slow lists (argument @classes.json, simadv --classes) and a guard
GFRAC=N/D env var (kappa 0: slow floor(N fmax/D), fast ceil(D fmin/N), Adm window [lo/g, hi*g]).]
Shard A, 2026-11-07 (UNTRUSTED, independent of simrunt.py's event loop and filter code): check a dumped run
against SpecRunt.GateOKRunt w with the read maps simrunt.py claims: non-LUT pins transport (f(t) = t - d); LUT pins
f(t) = greatest u <= t - d lying in no pulse narrower than w (Spec's Pulse: an interval between consecutive values
changes, including [0, first flip)). Checks, for every gate of the circuit (env-driven nodes excluded), at every
breakpoint t >= Gate.start: out(t) = INIT bit at the read address; every d inside Adm(g = 1, kappa, corner); for LUT
pins the read lag t - f(t) <= the Adm upper bound wherever a read lands in a narrow-pulse chain, and no read at
t >= start lands in a narrow power-up interval (no admissible f there). Delays rebuilt by the simadv/simrunt rule.
usage: gatecheck_runt.py net.json bnd.json dump.json corner kappa w SLOWNODE..."""
import json, sys, math, bisect
from fractions import Fraction as Fr
net = json.load(open(sys.argv[1])); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
BJ = json.load(open(sys.argv[2])); ENV = set(idx[x] for x in BJ["env"])
D = json.load(open(sys.argv[3])); c = Fr(sys.argv[4]); kap = Fr(sys.argv[5]); W = int(sys.argv[6])
ARCS = None
if len(sys.argv) > 7 and sys.argv[7].startswith("@"):
    ARCS = set((idx[x[0]], x[1]) for x in json.load(open(sys.argv[7][1:]))["S"]); sys.argv = sys.argv[:7]
import os
GF = os.environ.get("GFRAC"); gN, gD = map(int, GF.split("/")) if GF else (1, 1); gq = Fr(gN, gD)
SLOWN = set(idx[x] for x in sys.argv[7:])
drv = {g["out"]: gi for gi, g in enumerate(G) if g["out"] not in ENV}
SLOW = set(SLOWN)
for n0 in list(SLOWN):
    for u in G[drv[n0]]["ins"]:
        while u in drv and G[drv[u]]["k"] == 1 and G[drv[u]]["init"] == 2: SLOW.add(u); u = G[drv[u]]["ins"][0]
cs, kf = float(c), float(kap)
EXACT = (kap * 25).denominator == 1 and c == 0
P = int(kap * 25)
def islut(g): return g["name"].endswith("LUT.O6") or g["name"].endswith("LUT.O5")
def dly(e, slow, lut):
    if GF:
        assert P == 0 and c == 0
        d = (gN * e["fmax"]) // gD if slow else (gD * e["fmin"] + gN - 1) // gN
    elif EXACT: d = ((25 + P) * e["fmax"]) // 25 if slow else ((25 - P) * e["fmin"] + 24) // 25
    else:
        lo = (1 - cs) * e["fmin"] + cs * e["smin"]; hi = (1 - cs) * e["fmax"] + cs * e["smax"]
        d = int(math.floor(hi * (1 + kf))) if slow else int(math.ceil(lo * (1 - kf)))
    return max(d, W) if (lut and W) else d
def bounds(e):
    lo = (1 - c) * e["fmin"] + c * e["smin"]; hi = (1 - c) * e["fmax"] + c * e["smax"]
    return (1 - kap) * lo / gq, (1 + kap) * hi * gq
sig = {int(k): (bool(v[0]), v[1]) for k, v in D["nodes"].items()}
def raw(n): return sig.get(n, (False, []))
FILT = {}
def filtered(n):
    """(v0, flips, chains): the signal with every narrow interval replaced by the value before it; chains = list of
    (S, E) maximal runs of narrow intervals (reads in [S, E) are moved to S - 1)."""
    if n in FILT: return FILT[n]
    v0, fl = raw(n)
    bnd = [0] + fl                    # interval k = [bnd[k], bnd[k+1]) (last one open)
    vals = [v0 ^ (k % 2 == 1) for k in range(len(bnd))]
    narrow = [k + 1 < len(bnd) and bnd[k + 1] - bnd[k] < W for k in range(len(bnd))]
    fv = []; chains = []; cs_ = None
    for k in range(len(bnd)):
        if narrow[k]:
            fv.append(fv[-1] if k > 0 else None)
            if cs_ is None: cs_ = bnd[k]
        else:
            fv.append(vals[k])
            if cs_ is not None: chains.append((cs_, bnd[k])); cs_ = None
    f0 = fv[0]; ffl = []
    cur = f0
    for k in range(1, len(bnd)):
        if fv[k] is not None and fv[k] != cur: ffl.append(bnd[k]); cur = fv[k]
    FILT[n] = (f0, ffl, chains)
    return FILT[n]
def val(s, t):
    v0, fl = s[0], s[1]
    return bool(v0) ^ (bisect.bisect_right(fl, t) % 2 == 1)
tend = D["tend"]; bad = 0; badadm = 0; badlag = 0; badpow = 0; checked = 0; nlut = 0; maxlag = Fr(0)
for o, gi in drv.items():
    g = G[gi]; slow = o in SLOW; lut = islut(g) and W > 0; nlut += lut
    ds = [dly(e, slow if ARCS is None else (o, i) in ARCS, lut) for i, e in enumerate(g["arcs"])]
    for e, d in zip(g["arcs"], ds):
        lo, hi = bounds(e)
        if not (lo <= d <= hi): badadm += 1
    start = max([int(math.ceil((1 + kap) * e["smax"] * gq)) for e in g["arcs"]] + [0])
    ins = [(filtered(n) if lut else raw(n)) for n in g["ins"]]
    if lut:
        for i, n in enumerate(g["ins"]):
            lo, hi = bounds(g["arcs"][i])
            for (S, E) in ins[i][2]:
                if E - 1 + ds[i] < start: continue          # no read at t >= start lands in it
                if S == 0 or ins[i][0] is None: badpow += 1; continue
                lag = ds[i] + E - S
                maxlag = max(maxlag, lag - hi)
                if lag > hi: badlag += 1
    pts = {start}
    for i in range(len(ins)):
        for t in ins[i][1]: pts.add(t + ds[i])
    for t in raw(o)[1]: pts.add(t)
    for t in sorted(pts):
        if t < start or t > tend: continue
        a = sum((1 << i) for i in range(len(ins)) if val(ins[i], t - ds[i]))
        checked += 1
        if bool((g["init"] >> a) & 1) != val(raw(o), t):
            bad += 1
            if bad <= 5: print("MISMATCH gate", g["name"], "at", t)
print("gates", len(drv), "LUT gates filtered", nlut, "checks", checked, "mismatches", bad, "arcs outside Adm", badadm,
      "lag violations", badlag, "power-up chain reads", badpow, "worst lag - hi", float(maxlag), "tend", tend)
