#!/usr/bin/env python3
"""C-10m: cross-check tcheck's Jx prjxray columns (with the driver-side OUTMUX hop of
C-10h) against the auditor's independent model (audit/tc/xrc.py via rulej_x.py,
origin/claude/audit), client by client, and recompute the J over-credit table.

    python3 cmpxrc.py AUDIT_TC_DIR COMPARE_PREFIX [SEED...]
      AUDIT_TC_DIR    holds rulej_x.tsv (with OUTMUX) and rulej_x_nomux.tsv (XRC_NOMUX=1)
      COMPARE_PREFIX  e.g. results/compare5_  (compare2.py output, + SEED + .tsv)
Reporting only; no verdict depends on it."""
import csv
import re
import statistics
import sys

A, P = sys.argv[1], sys.argv[2]
SEEDS = sys.argv[3:] or ["d", "2", "3", "4"]


def load(p):
    out = {}
    for r in csv.DictReader(open(p), delimiter="\t"):
        if r["arb"] and r.get("ua_pin") and not r["ua_pin"].startswith("ERR"):
            out[(r["seed"], f"{r['arb']}#{r['k']}")] = r
    return out


M, N = load(f"{A}/rulej_x.tsv"), load(f"{A}/rulej_x_nomux.tsv")
cols = ["fast", "slow", "fastG", "slowG"]
dm, dn, n_in = [], [], 0
print("seed row | tcheck Jx f/s/fG/sG | xrc(OUTMUX) f/s/fG/sG | xrc(noMUX) | diff tc-xrc")
oc = {}
for s in SEEDS:
    for r in csv.DictReader(open(f"{P}{s}.tsv"), delimiter="\t"):
        if r["rule"] != "J":
            continue
        if r["flavour"] == "Jx" and r["tc_fast"] not in ("", "-"):
            key = (s, r["row"])
            if key not in M:
                continue
            m, n = M[key], N[key]
            t = [int(r["tc_" + c]) for c in cols]
            x = [int(m[c + "x"]) for c in cols]
            y = [int(n[c + "x"]) for c in cols]
            d = [a - b for a, b in zip(t, x)]
            dm.append(d); dn.append([a - b for a, b in zip(t, y)])
            n_in += all(abs(v) <= 15 for v in d)
            flag = ""
            if (min(t[2:]) < 0) != (min(x[2:]) < 0):
                flag = "  <-- band verdict differs"
            print(f"{s} {r['row'].replace('urig.udut.', '')} | {'/'.join(map(str, t))} | "
                  f"{'/'.join(map(str, x))} | {'/'.join(map(str, y))} | {'/'.join(map(str, d))}{flag}")
        if r["flavour"] == "Jx":
            mm = re.search(r"c_proj=(-?\d+) c_exact_sdf=(-?\d+)", r["note"])
            if mm:
                oc.setdefault(s, []).append(int(mm.group(1)) - int(mm.group(2)))
k = len(dm)
print(f"\nclients compared: {k}; all four columns within 15 ps of xrc(OUTMUX): {n_in}")
for nm, D in (("vs xrc OUTMUX", dm), ("vs xrc noMUX", dn)):
    if D:
        print(nm, "mean diff f/s/fG/sG:", [round(statistics.mean(d[i] for d in D), 1) for i in range(4)],
              "max |diff|:", [max(abs(d[i]) for d in D) for i in range(4)])
print("\nJ over-credit (c_proj - c_exact, SDF units; c_exact from prjxray SLOW_MAX shares incl. hop)")
for s in SEEDS:
    xs = oc.get(s, [])
    if xs:
        print(f"  seed {s}: n {len(xs)} mean {statistics.mean(xs):.0f} max {max(xs)} min {min(xs)} "
              f"under-credit rows {sum(1 for x in xs if x < 0)}")
