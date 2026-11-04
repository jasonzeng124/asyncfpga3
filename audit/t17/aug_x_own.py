#!/usr/bin/env python3
"""aug_x_own.py (audit T17): x = (board - FAST_MIN)/(SLOW_MAX - FAST_MIN) per vector from the owner's board table
(gcd_cost.tsv latmin) and two ps7_bench run logs; every simulated result checked against math.gcd; a batch whose
two runs disagree (latmin != latmax) or that did not complete is left out.
    python3 -I aug_x_own.py gcd_cost.tsv MIN.log MAX.log"""
import csv, math, re, sys, statistics as st
B = {(int(r["a"]), int(r["b"])): int(r["latmin"]) for r in csv.DictReader(open(sys.argv[1]), delimiter="\t")}
def runs(p):
    out = {}
    for m in re.finditer(r"BENCHRES .*?op0=([0-9a-f]+) op1=([0-9a-f]+) n=(\d+) completed=(\d+).*?latmin=(\d+) latmax=(\d+).*?odata=([0-9a-f]+) mism_st=(\d+)", open(p).read()):
        a, b = int(m.group(1), 16), int(m.group(2), 16)
        out[(a, b)] = dict(n=int(m.group(3)), done=int(m.group(4)), lo=int(m.group(5)), hi=int(m.group(6)),
                           res=int(m.group(7), 16), mism=int(m.group(8)))
    return out
lo, hi = runs(sys.argv[2]), runs(sys.argv[3])
wrong = [(k, c, d["res"]) for c, R in (("min", lo), ("max", hi)) for k, d in R.items() if d["res"] != math.gcd(*k)]
print("simulated results: min %d batches, max %d; wrong vs math.gcd: %d %s" % (len(lo), len(hi), len(wrong), wrong[:3]))
xs = []
for k, bl in B.items():
    a, b = lo.get(k), hi.get(k)
    ok = lambda d: d and d["done"] == d["n"] and d["lo"] == d["hi"]
    if not (ok(a) and ok(b)) or bl < 100:
        continue
    xs.append((bl - a["lo"]) / (b["lo"] - a["lo"]))
print("vectors used (both corners clean, board >= 100 cycles): %d; x median %.3f range %.3f-%.3f" % (len(xs), st.median(xs), min(xs), max(xs)))
