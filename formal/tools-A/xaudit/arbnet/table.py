"""table.py -- summarise xarbnet outputs (results/xan_<seed>_<corner>.txt): ArbOK and the part-2 rows.
UNTRUSTED reading of printed numbers.   python3 table.py [TAG]"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
tag = sys.argv[1] if len(sys.argv) > 1 else ""
KINDS = ["B1", "B2a", "B2b", "B2c", "Clo", "Chi", "N"]
print(f"| seed corner | ArbOK | OwnOK RsOK FixShape | " + " | ".join(f"{k} fail/min" for k in KINDS) + " |")
print("|" + "---|" * (3 + len(KINDS)))
for s in "d 3 4 5".split():
    for c in "slow fast indep gb".split():
        f = os.path.join(HERE, "results", f"xan_{s}_{c}{tag}.txt")
        if not os.path.exists(f):
            continue
        txt = open(f).read()
        m = re.search(r"ArbOK (\d+)/(\d+); OwnOK (\w+); RsOK (\w+); FixShape (\w+)", txt)
        if not m:
            print(f"| {s} {c} | (no result) |")
            continue
        vals = {k: [] for k in KINDS}
        for ln in txt.splitlines():
            if "ROW " not in ln:
                continue
            for k in KINDS:
                mm = re.search(rf" {k} (-?\d+)", ln)
                if mm:
                    vals[k].append(int(mm.group(1)))
        cells = []
        for k in KINDS:
            v = vals[k]
            cells.append(f"{sum(1 for x in v if x < 0)}/{len(v)} {min(v) if v else '-'}")
        print(f"| {s} {c} | {m.group(1)}/{m.group(2)} | {m.group(3)} {m.group(4)} {m.group(5)} | " + " | ".join(cells) + " |")
