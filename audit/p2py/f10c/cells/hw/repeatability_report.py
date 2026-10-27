#!/usr/bin/env python3
"""Split the measured scatter into within-programming and across-programming.

Reads the TSV written by hw/repeatability.sh.  The two terms answer different
questions and must not be pooled: WITHIN is what a repeated measurement of one
configuration costs you, ACROSS adds whatever reconfiguring the part changes.
Reported in ppm of the mean because the claims being checked are in percent.
"""
import sys, statistics as st
from collections import defaultdict

rows = defaultdict(lambda: defaultdict(list))
path = sys.argv[1] if len(sys.argv) > 1 else "build/hw/repeatability.tsv"
with open(path) as f:
    next(f)
    for ln in f:
        k, p, r, cyc, prep, lmin, lmax = ln.split()[:7]
        rows[k][int(p)].append((int(cyc), int(prep), int(lmin), int(lmax)))

def ppm(spread, mean):
    return spread / mean * 1e6 if mean else float("nan")

print()
print("kernel      progs batches  cycles/batch      within-prog        across-prog       latmin  latmax")
print("                                    mean   spread     ppm   spread     ppm")
for k, progs in rows.items():
    allc = [c for p in progs.values() for (c, _, _, _) in p]
    if not allc:
        continue
    mean = st.mean(allc)
    within = max(max(c for c, *_ in v) - min(c for c, *_ in v) for v in progs.values())
    permean = [st.mean([c for c, *_ in v]) for v in progs.values()]
    across = max(permean) - min(permean)
    lmin = min(l for p in progs.values() for (_, _, l, _) in p)
    lmax = max(l for p in progs.values() for (_, _, _, l) in p)
    print(f"{k:<11} {len(progs):>4} {len(allc):>7} {mean:>11.1f} {within:>8d} {ppm(within,mean):>7.0f} "
          f"{across:>8.1f} {ppm(across,mean):>7.0f} {lmin:>7d} {lmax:>7d}")
print()
print("within = worst spread of batch cycles inside a single programming")
print("across = spread of the per-programming MEANS (configuration noise, with")
print("         within-noise averaged down by the batch count)")
