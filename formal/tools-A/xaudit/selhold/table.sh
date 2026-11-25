#!/usr/bin/env bash
# E8SelC: one row per (seed, corner) from results/xs_<seed>_<corner>.txt (xselhold output) and the
# untrusted crosscheck results/cc_<seed>_<corner>.txt.  Output: results/table.txt
HERE="$(cd "$(dirname "$0")" && pwd)"
python3 -I - "$HERE/results" <<'EOF' | tee "$HERE/results/table.txt"
import re, sys, os
R = sys.argv[1]
print("| seed | corner | literals | entOK | src rows pass | min src margin (ps) | split rows pass | min split margin (ps) | verdict | crosscheck src / split |")
print("|---|---|---|---|---|---|---|---|---|---|")
for s in "d 3 4 5".split():
    for c in "slow fast gb indep".split():
        f = f"{R}/xs_{s}_{c}.txt"
        if not os.path.exists(f) or os.path.getsize(f) == 0:
            print(f"| {s} | {c} | missing |"); continue
        t = open(f).read()
        m1 = re.search(r"literals (\d+): entOK (\d+), chainOK (\d+), holdBand (\d+), all three (\d+); min hold margin (-?\d+)", t)
        m2 = re.search(r"split rows: (\d+) of (\d+) literals pass .*?; min split margin (-?\d+)", t)
        v = "CLEAN" if "SELHOLD(split) CLEAN" in t else re.search(r"SELHOLD\(split\) RESIDUAL (\d+)", t).group(0)
        cc = open(f"{R}/cc_{s}_{c}.txt").read() if os.path.exists(f"{R}/cc_{s}_{c}.txt") else ""
        m3 = re.search(r"min margin (-?\d+), min split margin (-?\d+)", cc)
        ccs = f"{m3.group(1)} / {m3.group(2)}" if m3 else "-"
        print(f"| {s} | {c} | {m1.group(1)} | {m1.group(2)} | {m1.group(5)} | {m1.group(6)} | {m2.group(1)} | {m2.group(3)} | {v} | {ccs} |")
EOF
