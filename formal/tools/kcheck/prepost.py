#!/usr/bin/env python3
"""Probe C-10n: row-by-row before/after of two kcheck result sets on the same routes
(e.g. tcheck's front end before and after C-10m's OUTMUX driver hop).
    python3 prepost.py KERNEL TAG        (results/KERNEL/rows.tsv vs results/KERNEL_TAG/rows.tsv)
Prints per rule/flavour: rows, rows whose tcheck margin moved (any variant), the largest move
per variant (after - before, ps; negative = tighter), and tcheck verdict flips."""
import pathlib, sys
from collections import defaultdict
H = pathlib.Path(__file__).resolve().parent
k, tag = sys.argv[1], sys.argv[2]
V = ["sdf", "sdfband", "fast", "slow", "fastG", "slowG"]


def load(d):
    out = {}
    for l in list(open(H / "results" / d / "rows.tsv"))[1:]:
        f = l.rstrip("\n").split("\t")
        out[(f[0], f[1], f[2], f[3])] = (f[7:13], f[13])
    return out


a, b = load(k), load(f"{k}_{tag}")
st = defaultdict(lambda: {"rows": 0, "moved": 0, "flip": [], **{v: 0 for v in V}, **{v + "+": 0 for v in V}})
for key in sorted(set(a) | set(b)):
    s = st[(key[1], key[2])]; s["rows"] += 1
    if key not in a or key not in b:
        s["flip"].append(f"{key[0]}:{key[3]} only in {'after' if key in b else 'before'}"); continue
    (ta, va), (tb, vb) = a[key], b[key]
    moved = False
    for v, x, y in zip(V, ta, tb):
        try:
            d = int(y) - int(x)
        except ValueError:
            continue
        if d:
            moved = True
            s[v] = min(s[v], d); s[v + "+"] = max(s[v + "+"], d)
    s["moved"] += moved
    if va != vb:
        s["flip"].append(f"s{key[0]} {key[3]}: {va}->{vb}")
print("rule\tflavour\trows\tmoved\t" + "\t".join(f"{v} min..max" for v in V) + "\tverdict flips")
for (r, fl), s in sorted(st.items()):
    print(f"{r}\t{fl}\t{s['rows']}\t{s['moved']}\t" + "\t".join(f"{s[v]}..{s[v+'+']}" for v in V)
          + "\t" + ("; ".join(s["flip"]) or "-"))
