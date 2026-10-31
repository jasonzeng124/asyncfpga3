#!/usr/bin/env python3
"""A_bandcheck.py (auditor P18): are the GLS SDF point delays that check_env.py uses (info.json: DA, per-reader Dr, Dq;
DQ1/DQ2 have no printed band) inside the xarbnet bands of the same route (slow/fast/gb/indep)?
   python3 -I A_bandcheck.py GLSQ_OUT2 ARBNET_RESULTS"""
import sys, json, re, os
o2, res = sys.argv[1], sys.argv[2]
pat = re.compile(r"arbiter (\S+)\.ustate\$LUT6: ArbOK \w+; K \d+, ctl lo \d+; Dq g1/g2/R0 \((\d+), (\d+)\)/\((\d+), (\d+)\)/\((\d+), (\d+)\), Dr1 g1/R0 \((\d+), (\d+)\)/\((\d+), (\d+)\), Dr2 g2/R0 \((\d+), (\d+)\)/\((\d+), (\d+)\), DA0 \((\d+), (\d+)\)")
def bands(f):
    B = {}
    for ln in open(f):
        m = pat.search(ln)
        if m:
            v = list(map(int, m.groups()[1:]))
            B[m.group(1)] = dict(g1=((v[6], v[7]), (v[0], v[1])), g2=((v[10], v[11]), (v[2], v[3])),
                                 s1=((v[8], v[9]), (v[4], v[5])), s2=((v[12], v[13]), (v[4], v[5])), DA=(v[14], v[15]))
    return B
for s in ("d", "3", "4", "5"):
    f = os.path.join(o2, f"env_{s}", "info.json")
    if not os.path.exists(f): continue
    info = json.load(open(f))
    for row in ("slow", "fast", "gb", "indep"):
        B = bands(os.path.join(res, f"xan_{s}_{row}.txt"))
        tot = bad = below = above = 0; ex = []
        for n, I in sorted(info.items()):
            b = B[n]
            arcs = [(f"{rd}.{k}", I["readers"][rd][k], b[rd][j]) for rd in ("g1", "g2", "s1", "s2") for j, k in ((0, "Dr"), (1, "Dq"))]
            arcs.append(("DA", I["DA"], b["DA"]))
            for nm, val, (lo, hi) in arcs:
                tot += 1
                if val < lo: bad += 1; below += 1; ex.append((n.split("udut.")[-1], nm, val, lo, hi))
                elif val > hi: bad += 1; above += 1; ex.append((n.split("udut.")[-1], nm, val, lo, hi))
        print(f"seed {s} {row}: {tot} arcs, {bad} outside the band ({below} below lo, {above} above hi)")
        if row == "indep":
            for e in ex: print("   ", e)
