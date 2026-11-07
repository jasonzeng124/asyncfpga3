#!/usr/bin/env python3
"""Shard B (UNTRUSTED), 2026-11-07: in a simb.py --dump, the pulses of width in [#delays, w) on the SOURCE node of a
support LUT pin whose admissible window (corner C, scatter K, g = 1) holds #delays < w integer read delays. Each such
pulse makes the run NOT a SpecRunt.BehavesRunt w behaviour (Formal.Cells.RuntForbid.runt_forbids), so the statement
NetCorrectSeqRunt w says nothing about that run. Also reports every pulse < w on any support LUT pin source (those that
the read-map form CAN skip).  usage: runtscan.py NET.json DUMP.json C K [W=20]"""
import json, sys, math
N = json.load(open(sys.argv[1])); D = json.load(open(sys.argv[2]))["nodes"]
C = float(sys.argv[3]); K = float(sys.argv[4]); W = int(sys.argv[5]) if len(sys.argv) > 5 else 20
def lut(g): return g["name"].endswith("LUT.O6") or g["name"].endswith("LUT.O5")
def dep(G, p):
    k, I = G["k"], G["init"]
    return any(((I >> a) & 1) != ((I >> (a | (1 << p))) & 1) for a in range(1 << k) if not a >> p & 1)
def npts(e):
    lo = (1 - K) * ((1 - C) * e["fmin"] + C * e["smin"]); hi = (1 + K) * ((1 - C) * e["fmax"] + C * e["smax"])
    return math.floor(hi + 1e-9) - math.ceil(lo - 1e-9) + 1
narrow = {}   # source node -> min #delays over narrow support pins reading it
allsrc = set()
for gi, g in enumerate(N["gates"]):
    if not lut(g): continue
    for p, (n, e) in enumerate(zip(g["ins"], g["arcs"])):
        if not dep(g, p): continue
        allsrc.add(n)
        m = npts(e)
        if m < W: narrow[n] = min(m, narrow.get(n, 99))
forb = []; skip = 0
for n in allsrc:
    if str(n) not in D: continue
    ts = D[str(n)][1]
    for a, b in zip(ts, ts[1:]):
        wdt = b - a
        if wdt < W:
            if n in narrow and wdt >= narrow[n]: forb.append((n, a, wdt, narrow[n]))
            else: skip += 1
print("narrow-window source nodes:", len(narrow), " sub-%d pulses on LUT-pin sources: %d skippable, %d FORBIDDEN" % (W, skip, len(forb)))
for n, a, wdt, m in sorted(forb, key=lambda x: x[1])[:20]:
    print("  node %d %s: pulse at %s ps, width %s, pin window %d delays" % (n, N["nodes"][n], a, wdt, m))
