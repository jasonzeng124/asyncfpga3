#!/usr/bin/env python3
"""C-10m: RT_FB (rule R / Rc) node by node, tcheck against the auditor's rtfb_x.py
(audit/tc/rtfb_<seed>.tsv, xrc model with OUTMUX).  Reporting only.

    python3 cmpxrc_r.py AUDIT_TC_DIR T5_PREFIX [SEED...]     (T5_PREFIX e.g. build/t5_)
Prints, per seed, the nodes where either tool's banded verdict is FAIL or the four margins
differ by more than 15 ps, plus the count within 15 ps.  The auditor's R takes the request
as a Dijkstra on prjxray LUT-only weights (SDF on MUXF arcs); tcheck's Rc is the checked
potential over the whole graph (C-10h), so differences in the request side are expected."""
import csv
import sys

A, P = sys.argv[1], sys.argv[2]
SEEDS = sys.argv[3:] or ["d", "2", "3", "4"]
C = ["fast", "slow", "fastG", "slowG"]
tot = within = 0
for s in SEEDS:
    try:
        X = {r["node"]: r for r in csv.DictReader(open(f"{A}/rtfb_{s}.tsv"), delimiter="\t")}
    except FileNotFoundError:
        continue
    m = {}
    for l in open(f"{P}{s}.out"):
        r = l.rstrip("\n").split("\t")
        lab = r[0].split()
        if lab[0] != "Rc" or r[2] == "none":
            continue
        m.setdefault(" ".join(lab[1:-2]), {})[lab[-2]] = int(r[2])
    n = w = 0
    for node, v in sorted(m.items()):
        if node not in X or any(c not in v for c in C) or v["sdf"] > 10 ** 11:
            continue
        x = X[node]
        try:
            xv = [int(x[c]) for c in C]
        except ValueError:
            continue
        t = [v[c] for c in C]
        d = [a - b for a, b in zip(t, xv)]
        n += 1
        ok = all(abs(q) <= 15 for q in d)
        w += ok
        if not ok and (min(t[2:]) < 100 or min(xv[2:]) < 100):
            print(f"{s} {node.replace('urig.udut.', '')} tc {'/'.join(map(str, t))} xrc {'/'.join(map(str, xv))} "
                  f"diff {'/'.join(map(str, d))}" + ("  <-- banded verdict differs" if (min(t[2:]) < 0) != (min(xv[2:]) < 0) else ""))
        elif min(t[2:]) < 0 or min(xv[2:]) < 0:
            print(f"{s} {node.replace('urig.udut.', '')} tc {'/'.join(map(str, t))} xrc {'/'.join(map(str, xv))} (within 15)")
    print(f"seed {s}: {n} nodes compared, {w} within 15 ps on all four columns")
    tot += n
    within += w
print(f"total {tot}, within 15 ps {within}")
