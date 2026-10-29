#!/usr/bin/env python3
"""usage: run_stats.py DUMP.tsv  -- auditor verdict (mystats) on both denominators + leave-one-out pass rate."""
import sys, csv, collections
sys.path.insert(0, "/home/user/asyncfpga3/audit/r15/ring")
import mystats as M
by = collections.defaultdict(list)
for r in csv.DictReader(open(sys.argv[1]), delimiter="\t"):
    by[r["sample"]].append(r)
for den in ("P_pre_ps", "P_np_ps"):
    S = [M.summ([(int(x["links"]), float(x["P_model_ps"]), float(x[den])) for x in v]) for v in by.values()]
    nin = 0
    print(f"== {sys.argv[1]} vs {den}: {len(S)} samples, {len(next(iter(by.values())))} rings each")
    for g in M.GR:
        vals = [s[g] for s in S]; lo, mi, hi = M.q(vals, .025), M.med(vals), M.q(vals, .975)
        ins = lo <= M.AUG[g] <= hi; nin += ins
        print(f"  {g:12s} {lo:8.3f} {mi:8.3f} {hi:8.3f}  Aug {M.AUG[g]:7.3f}  {'in' if ins else 'OUT'}")
    print(f"  graded inside: {nin}/7")
    if len(S) > 8:
        p, per = M.loo(S)
        print(f"  leave-one-out: a model sample passes all 7 in {p:.3f} of cases; per stat " + ", ".join(f"{g} {v:.2f}" for g, v in per.items()))
