#!/usr/bin/env python3
"""C-10h: old late side (10g: Dijkstra chain, H_EXTRACT_MIN) against the cert late side
(checked potential on the whole cyclic graph), per obligation and variant.
    python3 cmpcert.py build/t4_SEED.out [--tsv OUT]"""
import sys
from collections import defaultdict
V = ["sdf", "sdfband", "fast", "slow", "fastG", "slowG"]
rows = defaultdict(dict)
tags = defaultdict(dict)
for l in open(sys.argv[1]):
    f = l.rstrip("\n").split("\t")
    lab = f[0].split()
    rule, key, var = lab[0], lab[1], lab[-2]
    m = None if f[2] == "none" else int(f[2])
    if f[1] == "FAIL" and m is None:
        m = -10 ** 9
    rows[(rule, key)][var] = m
    tags[(rule, key)][var] = f[1]
out = ["rule\trow\tvariant\told\tcert\tdelta\told_verdict\tcert_verdict"]
stat = defaultdict(lambda: defaultdict(int))
for (rule, key), d in sorted(rows.items()):
    if not rule.endswith("c"):
        continue
    old = rows.get((rule[:-1], key), {})
    for v in V:
        n, o = d.get(v), old.get(v)
        if tags[(rule, key)].get(v) == "CERTBAD":
            stat[rule]["CERTBAD"] += 1
        if o is None:
            stat[rule]["no old instance"] += 1
            continue
        dl = n - o
        stat[rule]["equal" if dl == 0 else "cert lower" if dl < 0 else "cert HIGHER"] += 1
        if v in ("fastG", "slowG") and (n >= 0) != (o >= 0):
            stat[rule][f"verdict flip at {v}: old {'PASS' if o >= 0 else 'FAIL'} -> cert {'PASS' if n >= 0 else 'FAIL'}"] += 1
        if dl:
            out.append("\t".join(map(str, (rule, key, v, o, n, dl,
                                            tags[(rule[:-1], key)].get(v), tags[(rule, key)].get(v)))))
for r, d in stat.items():
    print(r, dict(d))
if "--tsv" in sys.argv:
    open(sys.argv[sys.argv.index("--tsv") + 1], "w").write("\n".join(out) + "\n")
