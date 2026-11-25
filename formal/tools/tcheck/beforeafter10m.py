#!/usr/bin/env python3
"""C-10m: before/after table of every tcheck row whose margin or verdict changed.

    python3 beforeafter10m.py BEFORE_DIR AFTER_DIR [SEED...]
      BEFORE_DIR / AFTER_DIR hold compare5_SEED.tsv (run4.sh/compare2.py), r10k_rows.tsv,
      r10l_rows.tsv and unchecked3.tsv (any may be missing).
Verdict = PASS iff fastG >= 0 and slowG >= 0 (tcheck's VERDICT).  Reporting only."""
import csv
import os
import sys

B, A = sys.argv[1], sys.argv[2]
SEEDS = sys.argv[3:] or ["d", "2", "3", "4"]
V = ["sdf", "sdfband", "fast", "slow", "fastG", "slowG"]


def num(x):
    try:
        return int(x)
    except (TypeError, ValueError):
        return None


def verdict(r):
    g = [num(r.get("fastG")), num(r.get("slowG"))]
    return None if None in g else ("PASS" if min(g) >= 0 else "FAIL")


def load_cmp(d, s):
    p = os.path.join(d, f"compare5_{s}.tsv")
    if not os.path.exists(p):
        return {}
    out = {}
    for r in csv.DictReader(open(p), delimiter="\t"):
        out[(s, r["rule"], r["flavour"], r["row"])] = {v: r["tc_" + v] for v in V}
    return out


def load_rows(d, name):
    p = os.path.join(d, name)
    if not os.path.exists(p):
        return {}
    out = {}
    for r in csv.DictReader(open(p), delimiter="\t"):
        # r10k/r10l: value may be "123" or "-45 FAIL"
        out[(r["seed"], r["rule"], "", r["obligation"])] = {v: (r[v] or "").split()[0] if r.get(v) else "" for v in V}
    return out


rows = []
for name, loader in (("compare5", None), ("r10k_rows.tsv", 1), ("r10l_rows.tsv", 1)):
    if loader is None:
        b, a = {}, {}
        for s in SEEDS:
            b.update(load_cmp(B, s)); a.update(load_cmp(A, s))
    else:
        b, a = load_rows(B, name), load_rows(A, name)
        if not a or not b:
            print(f"# {name}: not present in both directories, skipped")
            continue
        b = {k: v for k, v in b.items() if k[0] in SEEDS}
        a = {k: v for k, v in a.items() if k[0] in SEEDS}
    same = 0
    for k in sorted(set(b) | set(a)):
        x, y = b.get(k), a.get(k)
        if x == y:
            same += 1
            continue
        vb, va = (verdict(x) if x else "absent"), (verdict(y) if y else "absent")
        rows.append((name, *k, "/".join(x[v] for v in V[2:]) if x else "-",
                     "/".join(y[v] for v in V[2:]) if y else "-", vb, va,
                     "VERDICT CHANGES" if vb != va else ""))
    print(f"# {name}: {same} rows identical, {sum(1 for r in rows if r[0] == name)} changed")
print("table\tseed\trule\tflavour\trow\tbefore fast/slow/fastG/slowG\tafter\tverdict before\tafter\tflag")
for r in rows:
    print("\t".join(str(x) for x in r))
