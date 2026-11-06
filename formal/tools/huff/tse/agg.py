#!/usr/bin/env python3
"""aggregate tse2.py JSON lines: per pair min kappa* (sens, bisected), n traces, worst trace, slack at kappa 0
for sens and struct, unbounded counts. usage: agg.py out_*.txt"""
import json, sys, collections, math
rows = collections.defaultdict(list)
for f in sys.argv[1:]:
    for l in open(f):
        if l.startswith("JSON "): r = json.loads(l[5:]); rows[r["pair"]].append(r)
def kk(r, m):
    k = r[m]["k"]
    return -9 if k is None else k
print("%-34s %3s  %-14s %-14s %-9s  %-21s %-21s %s" % ("pair c__b", "n", "k*sens fast", "k*sens slow", "unb s/st", "min slack0 sens f/s", "min slack0 struct f/s", "worst trace (A, HI(A->c')+loop, LO(A->b) fast)"))
for pair in sorted(rows, key=lambda p: min(kk(r, "sens/s") for r in rows[p])):
    rs = rows[pair]
    def mk(m):
        ks = [r[m]["k"] for r in rs]
        if any(k is None for k in ks): return "unb(%d)" % sum(k is None for k in ks)
        m0 = min(ks); return "%.3f" % m0 if m0 >= 0 else "FAIL"
    def ms(m):
        v = min((r[m]["s0"] for r in rs), key=lambda x: -x)  # worst = largest slack
        return "%.0f" % v
    unb = "%d/%d" % (sum(r["sens/f"]["k"] is None for r in rs), sum(math.isinf(r["struct/f"]["s0"]) for r in rs))
    w = min(rs, key=lambda r: kk(r, "sens/f"))
    d = w["sens/f"]
    print("%-34s %3d  %-14s %-14s %-9s  %-21s %-21s %s  %s  %.0f+%d / %.0f" % (pair, len(rs), mk("sens/f"), mk("sens/s"), unb,
          ms("sens/f") + "/" + ms("sens/s"), ms("struct/f") + "/" + ms("struct/s"), w["base"].split("__")[-1], d["A"], d["HA"], d["loop"], d["LA"]))
