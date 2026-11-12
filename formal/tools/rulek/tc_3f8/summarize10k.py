#!/usr/bin/env python3
"""Probe C-10k report (evidence only; no verdict depends on it): per-row margins of
rules Fd, Z, X, Xi under every corner model, per seed, from build/t10k_SEED.out.

    python3 summarize10k.py d 2 3 4
-> results/r10k_rows.tsv   seed rule obligation, then margin and verdict per variant
   results/summary10k.txt  per rule and variant: rows, FAIL count, min margin (seed)
"""
import sys
from collections import defaultdict

V = ["sdf", "sdfband", "fast", "slow", "fastG", "slowG"]


def main(seeds):
    rows = defaultdict(dict)        # (seed, rule, obl) -> {v: (tag, margin)}
    for s in seeds:
        try:
            lines = open(f"build/t10k_{s}.out").read().splitlines()
        except OSError:
            continue
        for ln in lines:
            f = ln.split("\t")
            head = f[0].split(" ")
            rule, v = head[0], head[-2]
            obl = " ".join(head[1:-2]).replace("urig.udut.", "")
            m = int(f[2]) if f[2] not in ("none", "") else None
            rows[(s, rule, obl)][v] = (f[1], m)
    with open("results/r10k_rows.tsv", "w") as out:
        out.write("seed\trule\tobligation\t" + "\t".join(V) + "\n")
        for (s, r, o), d in sorted(rows.items()):
            out.write(f"{s}\t{r}\t{o}\t" + "\t".join(
                (f"{d[v][1]}{'' if d[v][0] == 'PASS' else ' ' + d[v][0]}" if v in d else "-") for v in V) + "\n")
    lines = []
    rules = sorted({r for (_, r, _) in rows})
    for r in rules:
        lines.append(f"rule {r}")
        for s in seeds:
            keys = [k for k in rows if k[0] == s and k[1] == r]
            if not keys:
                continue
            parts = []
            for v in V:
                ms = [(rows[k][v][1], k[2]) for k in keys if v in rows[k] and rows[k][v][1] is not None]
                nf = sum(1 for k in keys if v in rows[k] and rows[k][v][0] != "PASS")
                mn = min(ms) if ms else (None, "")
                parts.append(f"{v}: fail {nf} min {mn[0]}")
            lines.append(f"  seed {s}: {len(keys)} rows; " + "; ".join(parts))
        bad = sorted({(k[0], k[2], v, rows[k][v][1]) for k in rows if k[1] == r
                      for v in V if v in rows[k] and rows[k][v][0] != "PASS"})
        for b in bad:
            lines.append(f"    FAIL seed {b[0]} {b[2]} {b[3]}  {b[1]}")
    open("results/summary10k.txt", "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main(sys.argv[1:] or ["d", "2", "3", "4"])
