#!/usr/bin/env python3
"""Probe C-10l report (evidence only; no verdict depends on it): per-row margins of the
credited rules Xc, Xic, Xm and K under every corner model, per seed, from
build/t10l_SEED.out, next to the uncredited X / Xi rows of build/t10k_SEED.out; the
Fd diagnostics (shared-element two-edge charge) from build/obl10l_SEED.json.

    python3 summarize10l.py d 2 3 4
-> results/r10l_rows.tsv   seed rule obligation, then margin (and verdict if not PASS) per variant
   results/summary10l.txt  per rule and variant: rows, FAIL count, min margin; FAIL list;
                           per Xm row the uncredited X / Xi margins; Fd diagnostics
"""
import json
import sys
from collections import defaultdict

V = ["sdf", "sdfband", "fast", "slow", "fastG", "slowG"]


def load(path, rows, s):
    try:
        lines = open(path).read().splitlines()
    except OSError:
        return
    for ln in lines:
        f = ln.split("\t")
        if len(f) < 3:
            continue
        head = f[0].split(" ")
        rule, v = head[0], head[-2]
        obl = " ".join(head[1:-2]).replace("urig.udut.", "")
        m = int(f[2]) if f[2] not in ("none", "") else None
        rows[(s, rule, obl)][v] = (f[1], m)


def main(seeds):
    rows = defaultdict(dict)
    old = defaultdict(dict)
    for s in seeds:
        load(f"build/t10l_{s}.out", rows, s)
        load(f"build/t10k_{s}.out", old, s)
    with open("results/r10l_rows.tsv", "w") as out:
        out.write("seed\trule\tobligation\t" + "\t".join(V) + "\n")
        for (s, r, o), d in sorted(rows.items()):
            out.write(f"{s}\t{r}\t{o}\t" + "\t".join(
                (f"{d[v][1]}{'' if d[v][0] == 'PASS' else ' ' + d[v][0]}" if v in d else "-") for v in V) + "\n")
    lines = []
    for r in sorted({r for (_, r, _) in rows}):
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
        bad = sorted({(k[0], k[2], v, rows[k][v][0], rows[k][v][1]) for k in rows if k[1] == r
                      for v in V if v in rows[k] and rows[k][v][0] != "PASS"})
        for b in bad:
            lines.append(f"    {b[3]} seed {b[0]} {b[2]} {b[4]}  {b[1]}")
    # the uncredited rows that failed, and what the credited rules say about them
    lines.append("previously failing X / Xi rows (C-10k) -> Xc / Xic / Xm (min over the failing variants)")
    for (s, r, o), d in sorted(old.items()):
        if r not in ("X", "Xi"):
            continue
        fv = [v for v in V if v in d and d[v][0] != "PASS"]
        if not fv:
            continue
        def get(rr):
            e = rows.get((s, rr, o))
            if not e:
                return "-"
            return " ".join(f"{v}:{e[v][1]}{'' if e[v][0] == 'PASS' else '!'}" for v in fv if v in e)
        lines.append(f"  seed {s} {r} {o}: was " + " ".join(f"{v}:{d[v][1]}" for v in fv)
                     + f" | Xc {get('Xc')} | Xic {get('Xic')} | Xm {get('Xm')}")
    lines.append("Fd diagnostics (least-margin pairs; shared = arcs on both critical paths)")
    for s in seeds:
        try:
            m = json.load(open(f"build/obl10l_{s}.json"))["obligations"]
        except OSError:
            continue
        for o in m:
            if "diag" not in o:
                continue
            for v in ("fastG", "slowG", "sdfband", "slow"):
                for row in o["diag"].get(v, [])[:2]:
                    lines.append(f"  seed {s} {o['label'].replace('urig.udut.', '')} {v}: "
                                 f"margin {row['margin']} (data {row['data']}, late {row['late']}) "
                                 f"stage {row['stage']} shared {row['shared']} credit {row['shared_credit']}"
                                 f" -> {row['margin'] + row['shared_credit']}  {row['shared_arcs'][:3]}")
    open("results/summary10l.txt", "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main(sys.argv[1:] or ["d", "2", "3", "4"])
