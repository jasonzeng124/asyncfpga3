#!/usr/bin/env python3
"""C-10l2: per tag (K, Kold, Knoblk, Knocmax, Knolat) and corner variant: rows, FAIL count,
min margin, from tcheck outputs.   summ.py OUT [OUT...]   (OUT = build/out/k_SEED.out)"""
import sys
from collections import defaultdict
V = ["sdf", "sdfband", "fast", "slow", "fastG", "slowG"]
for path in sys.argv[1:]:
    st = defaultdict(lambda: defaultdict(list))
    for ln in open(path):
        f = ln.rstrip("\n").split("\t")
        if len(f) < 3:
            continue
        head = f[0].split(" ")
        tag, v = head[0], head[-2]
        m = int(f[2]) if f[2] not in ("none", "") else None
        st[tag][v].append((f[1], m, " ".join(head[1:-2]).replace("urig.udut.", "")))
    print(path)
    for tag in sorted(st):
        parts = []
        for v in V:
            L = st[tag][v]
            nf = sum(1 for r in L if r[0] != "PASS")
            ms = [r[1] for r in L if r[1] is not None]
            parts.append(f"{v}: {nf}/{len(L)} fail, min {min(ms) if ms else None}")
        print(f"  {tag:8s} " + "; ".join(parts))
