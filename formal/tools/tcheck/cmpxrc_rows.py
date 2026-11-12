#!/usr/bin/env python3
"""C-10m: rules E, A, F row by row, tcheck (results/compare5_SEED.tsv) against the auditor's
tables (origin/claude/audit audit/tc/: rulee_*.tsv from rulee_x.py, tighten_corners2_*.tsv
from tighten.py run on single-corner SDFs).  Reporting only.

    python3 cmpxrc_rows.py AUDIT_TC_DIR COMPARE_PREFIX [SEED...]

The algorithms differ by design, so only the banded columns of comparable flavours are set
side by side and the differences are expected to be non-zero:
  E0 (tcheck: min over skew's launches, no credit)  vs  audit fastG0/slowG0 (skew's worst
     guarded launch, no credit)
  E  (tcheck: dominator credit, H_CLEAN_EDGE)       vs  audit fastG/slowG (skew's measured
     path credit)
  A, F (tcheck: all-paths race under the band)      vs  audit fastG/slowG (tighten's walk on
     corner SDFs, per-arc band)
What is reported: rows, rows within 15 ps on both columns, rows where the banded verdicts
differ (listed), the audit table used per seed (full = MUXF modelled, fbs = fallback scaled,
plain = LUT-only)."""
import csv
import os
import sys

A, P = sys.argv[1], sys.argv[2]
SEEDS = sys.argv[3:] or ["d", "2", "3", "4"]


def load(name):
    p = os.path.join(A, name)
    return list(csv.DictReader(open(p), delimiter="\t")) if os.path.exists(p) else None


def num(x):
    try:
        return int(x)
    except (TypeError, ValueError):
        return None


for s in SEEDS:
    tc = {}
    for r in csv.DictReader(open(f"{P}{s}.tsv"), delimiter="\t"):
        tc[(r["rule"], r["flavour"], r["row"])] = (num(r["tc_fastG"]), num(r["tc_slowG"]))
    for tab in ("full", "fbs", "plain"):
        E = load(f"rulee_{tab}_{s}.tsv" if tab != "plain" else f"rulee_{s}.tsv")
        if E:
            break
    if E:
        for fl, cols in (("E0", ("fastG0", "slowG0")), ("E", ("fastG", "slowG"))):
            n = w = 0
            diffs = []
            for r in E:
                key = ("E", fl, r["gate"])
                if key not in tc or None in tc[key]:
                    continue
                x = (num(r[cols[0]]), num(r[cols[1]]))
                if None in x:
                    continue
                t = tc[key]
                n += 1
                w += abs(t[0] - x[0]) <= 15 and abs(t[1] - x[1]) <= 15
                if (min(t) < 0) != (min(x) < 0):
                    diffs.append(f"    {r['gate'].replace('urig.udut.', '')}: tcheck {t[0]}/{t[1]} audit {x[0]}/{x[1]}")
            print(f"seed {s} {fl} vs audit rulee ({tab}) {cols[0]}/{cols[1]}: {n} gates, within 15 ps {w}, "
                  f"banded verdict differs {len(diffs)}")
            print("\n".join(diffs))
    T = load(f"tighten_corners2_{s}.tsv")
    if T:
        for rule in ("A", "F"):
            n = w = 0
            diffs = []
            for r in T:
                if r["rule"] != rule:
                    continue
                cand = [k for k in tc if k[0] == rule and k[2].endswith("." + r["row"]) or k[2] == r["row"]]
                cand = [k for k in cand if k[0] == rule and (k[1] in ("A", "Fc"))]
                if len(cand) != 1 or None in tc[cand[0]]:
                    continue
                t = tc[cand[0]]
                x = (num(r["fastG"]), num(r["slowG"]))
                if None in x:
                    continue
                n += 1
                w += abs(t[0] - x[0]) <= 15 and abs(t[1] - x[1]) <= 15
                if (min(t) < 0) != (min(x) < 0):
                    diffs.append(f"    {r['row']}: tcheck {t[0]}/{t[1]} audit {x[0]}/{x[1]}")
            print(f"seed {s} {rule} vs audit tighten_corners2: {n} rows, within 15 ps {w}, banded verdict differs {len(diffs)}")
            print("\n".join(diffs))
