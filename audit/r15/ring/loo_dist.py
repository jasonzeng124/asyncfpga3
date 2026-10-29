#!/usr/bin/env python3
"""LOO distribution of the number of graded stats a model sample misses (auditor)."""
import sys, csv, collections
sys.path.insert(0, "/home/user/asyncfpga3/audit/r15/ring"); import mystats as M
by = collections.defaultdict(list)
for r in csv.DictReader(open(sys.argv[1]), delimiter="\t"): by[r["sample"]].append(r)
for den in ("P_pre_ps", "P_np_ps"):
    S = [M.summ([(int(x["links"]), float(x["P_model_ps"]), float(x[den])) for x in v]) for v in by.values()]
    c = collections.Counter()
    for i, s in enumerate(S):
        rest = S[:i] + S[i+1:]
        c[sum(1 for g in M.GR if not (M.q([r[g] for r in rest], .025) <= s[g] <= M.q([r[g] for r in rest], .975)))] += 1
    print(den, "misses: " + ", ".join(f"{k}:{c[k]}" for k in sorted(c)), f" P(>=3 misses)={sum(v for k,v in c.items() if k>=3)/len(S):.3f}  P(>=1)={1-c[0]/len(S):.3f}")
