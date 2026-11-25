#!/usr/bin/env python3
"""C-10o summary: exact rows (rows_R.json) + tcheck Fd/Fu verdicts (t_R.out) + project rule F.

    python3 summarize.py build > results.txt
Also writes build/compare_F.tsv (one line per FASTFALL line, route, variant) and
build/rows_FR.tsv (worst uack rows).
"""
import collections
import glob
import json
import os
import re
import sys

D = sys.argv[1]
V = ["sdf", "sdfband", "fast", "slow", "fastG", "slowG"]


def tchk(path):
    out = {}
    if not os.path.exists(path):
        return out
    for line in open(path):
        f = line.rstrip("\n").split("\t")
        if len(f) < 3:
            continue
        lab = f[0].split()
        rule, base, var = lab[0], lab[1], lab[3]
        try:
            m = int(f[2])
        except ValueError:
            m = None
        out[(rule, base, var)] = (f[1], m)
    return out


routes = sorted(os.path.basename(p)[5:-5] for p in glob.glob(f"{D}/rows_*.json"))
tsv = open(f"{D}/compare_F.tsv", "w")
tsv.write("route\tline\tn\tvariant\truleF_margin(sdf)\tFd\tFd_margin\texact\tT\tTstar\t"
          "exact_margin\tstage_margin\n")
frw = open(f"{D}/rows_FR.tsv", "w")
frw.write("route\tline\tn\tvariant\tFu\tFu_margin\texact\tT\tTstar\texact_margin\tstage_margin\n")
print("C-10o chainck summary (exact rows = Python mirror of ChainSettle.Lc; Fd/Fu = tcheck "
      "pverdict, proved)")
tot = collections.Counter()
flips = []
for R in routes:
    rows = json.load(open(f"{D}/rows_{R}.json"))
    tc = tchk(f"{D}/t_{R}.out")
    sha = open(f"{D}/sha_{R}.txt").read().split()[0][:12] if os.path.exists(f"{D}/sha_{R}.txt") else "?"
    print(f"\n== {R}  (fasm sha {sha})  chains: "
          f"{sum(r['kind'] == 'FF' for r in rows)} FASTFALL, {sum(r['kind'] == 'FR' for r in rows)} "
          f"FASTRISE uack; skipped {sum('skip' in r for r in rows)}")
    for kind, rule in (("FF", "Fd"), ("FR", "Fu")):
        for v in V:
            rs = [r for r in rows if r["kind"] == kind and "v" in r and "pass" in r["v"].get(v, {})]
            if not rs:
                continue
            ex_f = [r for r in rs if not r["v"][v]["pass"]]
            tcs = [tc.get((rule, r["base"], v)) for r in rs]
            tc_f = [x for x in tcs if x and x[0] != "PASS"]
            tc_m = [x[1] for x in tcs if x and x[1] is not None]
            me = min(rs, key=lambda r: r["v"][v]["margin_exact"])
            ms = [r["v"][v]["margin_stage"] for r in rs if r["v"][v]["margin_stage"] is not None]
            fb = sum(r["v"][v]["fallback"] > 0 for r in rs)
            print(f"  {kind} {v:<8} rows {len(rs):>3}  exact FAIL {len(ex_f):>2}  min exact "
                  f"{me['v'][v]['margin_exact']:>6} ({me['base'].replace('urig.udut.', '')})  "
                  f"min stage {min(ms) if ms else '-':>6}  {rule} FAIL {len(tc_f):>2} "
                  f"(missing {sum(x is None for x in tcs)}) min {min(tc_m) if tc_m else '-':>6}"
                  f"  rows w/ fallback arcs {fb}")
            tot[(kind, v, "rows")] += len(rs)
            tot[(kind, v, "exactFAIL")] += len(ex_f)
            tot[(kind, v, "tcFAIL")] += len(tc_f)
    for r in rows:
        if "v" not in r:
            continue
        for v in V:
            x = r["v"].get(v, {})
            if "pass" not in x:
                continue
            if r["kind"] == "FF":
                rf = r.get("ruleF", {}).get("margin")
                t = tc.get(("Fd", r["base"], v), ("-", None))
                tsv.write(f"{R}\t{r['base']}\t{r['n']}\t{v}\t{rf}\t{t[0]}\t{t[1]}\t"
                          f"{'PASS' if x['pass'] else 'FAIL'}\t{x['T']}\t{x['Tstar']}\t"
                          f"{x['margin_exact']}\t{x['margin_stage']}\n")
                if rf is not None and (rf >= 0) != x["pass"]:
                    flips.append((R, r["base"], v, rf, x["margin_exact"], t))
                if t[0] != "-" and (t[0] == "PASS") != x["pass"]:
                    flips.append((R, r["base"], v, "Fd-vs-exact", x["margin_exact"], t))
            else:
                t = tc.get(("Fu", r["base"], v), ("-", None))
                frw.write(f"{R}\t{r['base']}\t{r['n']}\t{v}\t{t[0]}\t{t[1]}\t"
                          f"{'PASS' if x['pass'] else 'FAIL'}\t{x['T']}\t{x['Tstar']}\t"
                          f"{x['margin_exact']}\t{x['margin_stage']}\n")
print("\n== totals")
for kind in ("FF", "FR"):
    for v in V:
        if tot[(kind, v, "rows")]:
            print(f"  {kind} {v:<8} rows {tot[(kind, v, 'rows')]:>4}  exact FAIL "
                  f"{tot[(kind, v, 'exactFAIL')]:>3}  tcheck {'Fd' if kind == 'FF' else 'Fu'} FAIL "
                  f"{tot[(kind, v, 'tcFAIL')]:>3}")
print("\n== disagreements (rule F sdf margin sign vs exact verdict; Fd verdict vs exact verdict)")
for f in flips:
    print("  ", f)
