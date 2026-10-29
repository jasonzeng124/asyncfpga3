#!/usr/bin/env python3
"""Recompute BQ#3 full-stack rows from bq3_fullstack_8seed.tsv: last row per (seed, column)."""
import sys, statistics as st
last = {}
for ln in open(sys.argv[1]):
    if ln.startswith("#") or not ln.strip(): continue
    p = ln.rstrip("\n").split("\t"); last[(p[0], p[1])] = p
cols = sorted({k[1] for k in last})
for c in cols:
    rows = [last[k] for k in sorted(last) if k[1] == c]
    seeds = [r[0] for r in rows]; ok = [r[0] for r in rows if r[4] == "PASS"]
    L = [[int(x) for x in r[7].split("/")] for r in rows]
    print(f"{c:22s} n={len(rows)} seeds={','.join(seeds)} pass={len(ok)} " + " ".join(
        f"v{v}: mean {st.mean(l[i] for l in L):.2f} ({min(l[i] for l in L)}-{max(l[i] for l in L)})" for i, v in enumerate((6, 12, 13))))
