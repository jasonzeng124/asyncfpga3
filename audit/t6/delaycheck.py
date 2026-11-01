#!/usr/bin/env python3
"""T6: check shard B's delay assignment against Spec.Adm (g = 1, kappa, corner c) with exact rationals.
For every arc of every gate of the LEAN net (B's lean2json output) compute (a) B's integer delay exactly as
simb.py's dly() computes it (floats), (b) my exact Adm interval, and report any delay outside it.
Also prints the posmap gates' delays and the path sums around ua1.
usage: delaycheck.py LEAN_NET.json POSMAP KAPPA [CORNER]"""
import json, math, sys
from fractions import Fraction as Fr
NET, PMF, K = sys.argv[1:4]
C = sys.argv[4] if len(sys.argv) > 4 else "0.5"
c, k = float(C), float(K)
cq, kq = Fr(C), Fr(K)
N = json.load(open(NET)); G = N["gates"]
raw = json.load(open(PMF))
PM = {int(x): v for x, v in raw.items() if ":" not in x}
PP = {tuple(map(int, x.split(":"))): v for x, v in raw.items() if ":" in x}

def b_dly(e, gi, pin):   # verbatim logic of simb.py dly() with g = 1, scatter 0
    lo = (1 - c) * e["fmin"] + c * e["smin"]; hi = (1 - c) * e["fmax"] + c * e["smax"]
    pp = PP.get((gi, pin), PM.get(gi, 0.5))
    if pp == -1:
        d = max((1 - k) * lo, e["fmin"] / 1.0); return int(-(-d // 1))
    if pp == 2:
        d = min((1 + k) * hi, e["smax"] * 1.0); return int(d // 1)
    return int(round(lo + pp * (hi - lo)))

def adm(e):
    llo = (1 - cq) * e["fmin"] + cq * e["smin"]; lhi = (1 - cq) * e["fmax"] + cq * e["smax"]
    return (max(Fr(e["fmin"]), (1 - kq) * llo), min(Fr(e["smax"]), (1 + kq) * lhi))

bad = 0; n = 0; tight = []
for gi, g in enumerate(G):
    for pin, e in enumerate(g["arcs"]):
        d = b_dly(e, gi, pin); lo, hi = adm(e); n += 1
        if not (lo <= d <= hi):
            bad += 1
            if bad <= 10: print("OUTSIDE", gi, g["name"], pin, d, float(lo), float(hi))
        if gi in PM or (gi, pin) in PP:
            # also the kappa-0 window (Adm at kappa = 0) to show how far outside the corner window it is
            l0 = (1 - cq) * e["fmin"] + cq * e["smin"]; h0 = (1 - cq) * e["fmax"] + cq * e["smax"]
            tight.append((gi, pin, g["name"], d, float(lo), float(hi), float(l0), float(h0)))
print("arcs checked %d, outside Adm(g=1, kappa=%s, c=%s): %d" % (n, K, C, bad))
print("posmap arcs: gate pin name | delay | Adm window | kappa-0 corner window")
for t in tight:
    print("  %6d %d %-55s %4d  [%.2f, %.2f]  [%.1f, %.1f]" % t)
# path sums (ua1 = gate 109800)
def ds(gi): return [b_dly(e, gi, p) for p, e in enumerate(G[gi]["arcs"])]
fast = [(109724, 0), (109744, 0), (255, 0), (256, 0), (261, 4), (109777, 0), (109796, 0), (109800, 4)]
loop = [(109785, 0), (109786, 0), (109787, 0), (109800, 0)]
print("g-path ua1 -> ua1.pin4 (D5):", [ds(g)[p] for g, p in fast], "sum", sum(ds(g)[p] for g, p in fast))
print("fb loop ua1 -> ua1.pin0 (D1):", [ds(g)[p] for g, p in loop], "sum", sum(ds(g)[p] for g, p in loop))
