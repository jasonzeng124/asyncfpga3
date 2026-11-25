#!/usr/bin/env bash
# E9SelRun: one row per (seed, corner) from results/xl_<seed>_<corner>.txt (xselL) and, for comparison,
# E8SelC's selhold/results/xs_<seed>_<corner>.txt (src / split rows, H_ACK_LAG assumed).  -> results/table.txt
HERE="$(cd "$(dirname "$0")" && pwd)"
python3 -I - "$HERE/results" "$HERE/../selhold/results" <<'PY' | tee "$HERE/results/table.txt"
import re, sys, os
R, E = sys.argv[1], sys.argv[2]
print("| seed | corner | recog+log | literals | entOK | treeOK | reqOK | selL pass | selT pass | selT min (ps) | selJ pass | selJ min (ps) | E8SelC src / split min (ps) | verdict (selJ) |")
print("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
for s in "d 3 4 5".split():
    for c in "slow fast gb indep".split():
        f = f"{R}/xl_{s}_{c}.txt"
        if not os.path.exists(f) or os.path.getsize(f) == 0:
            print(f"| {s} | {c} | missing |"); continue
        t = open(f).read()
        rc = "ok" if re.search(r"Recog6 true; Net4.OK7 true; .*accepted by runLog: true", t) else "NO"
        m1 = re.search(r"literals (\d+): entOK (\d+), treeOK (\d+), reqOK (\d+)", t)
        m2 = re.search(r"selL rows (\d+)/\d+ \(min margin (-?\d+) ps\); selT rows (\d+)/\d+ \(min margin (-?\d+) ps\); selJ rows (\d+)/\d+ \(min margin (-?\d+) ps\)", t)
        v = re.search(r"^SELJ (.*)$", t, re.M).group(1)
        e = f"{E}/xs_{s}_{c}.txt"
        es = "-"
        if os.path.exists(e):
            et = open(e).read()
            a = re.search(r"min hold margin (-?\d+)", et); b = re.search(r"min split margin (-?\d+)", et)
            es = f"{a.group(1)} / {b.group(1)}"
        print(f"| {s} | {c} | {rc} | {m1.group(1)} | {m1.group(2)} | {m1.group(3)} | {m1.group(4)} | {m2.group(1)} | {m2.group(3)} | {m2.group(4)} | {m2.group(5)} | {m2.group(6)} | {es} | {v} |")
PY
