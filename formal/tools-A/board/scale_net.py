#!/usr/bin/env python3
"""scale_net.py (shard A, 2026-11-17): a decoded net with every arc placed at one point of its prjxray band.

    python3 scale_net.py NET.json OUT.json B_R B_C

Each arc's delay becomes FAST_MIN + b (SLOW_MAX - FAST_MIN), with b = B_C for CARRY4 and MUXF7/F8 arcs (kinds carry,
muxf) and b = B_R for every other arc (LUT pins + IOPATH, pips, site hops), research's two-band draw model
(FOR-FORMAL 2026-11-16) without the within-die factors. All four band numbers of the arc are set to that delay, so
simx at --corner 0 --kappa 0 --cdefault F runs exactly these delays.
"""
import json, sys
net = json.load(open(sys.argv[1])); br, bc = float(sys.argv[3]), float(sys.argv[4])
for g in net["gates"]:
    b = bc if g["kind"] in ("carry", "muxf") else br
    for a in g["arcs"]:
        d = int(round(a["fmin"] + b * (a["smax"] - a["fmin"])))
        a["fmin"] = a["fmax"] = a["smin"] = a["smax"] = d
json.dump(net, open(sys.argv[2], "w"))
