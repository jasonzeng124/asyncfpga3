#!/usr/bin/env python3
"""ssta_table.py OUT [TOP] -- research/tools/ssta_draws.sh's draws summarised: per constraint the raw margin (no guard)
over the draws -- n, mean, sd, minimum, how many draws below 0, and the normal tail P(margin < 0) at the measured mean
and sd -- worst first by that tail; then per draw, how many constraints were below 0 (a draw with one is a draw in
which the rule says some race is lost).  TOP (default 25) rows."""
import glob
import math
import os
import statistics as st
import sys


def main():
    out = sys.argv[1]
    top = int(sys.argv[2]) if len(sys.argv) > 2 else 25
    per, draws = {}, []
    for f in sorted(glob.glob(os.path.join(out, "d*", "raw", "all_constraints.tsv"))):
        k = os.path.basename(os.path.dirname(os.path.dirname(f)))[1:]
        neg = 0
        for ln in open(f):
            w = ln.rstrip("\n").split("\t")
            if w[0] == "rule" or len(w) < 3:
                continue
            m = int(w[1])
            per.setdefault(w[2], []).append(m)
            neg += m < 0
        draws.append((k, neg))
    n = len(draws)
    if not n:
        sys.exit("ssta_table: no draws in %s" % out)
    rows = []
    for key, ms in per.items():
        mu = st.mean(ms)
        sd = st.pstdev(ms) if len(ms) > 1 else 0.0
        tail = 0.5 * math.erfc(mu / sd / math.sqrt(2)) if sd > 0 else (1.0 if mu < 0 else 0.0)
        rows.append((tail, key, len(ms), mu, sd, min(ms), sum(1 for m in ms if m < 0)))
    rows.sort(key=lambda r: (-r[0], r[3]))
    print("%d draws, %d constraints (sized rules, raw margins: no guard)" % (n, len(rows)))
    print("%-9s %-5s %8s %6s %7s %5s  %s" % ("P(<0)", "n", "mean", "sd", "min", "<0", "constraint"))
    for tail, key, cnt, mu, sd, mn, nn in rows[:top]:
        print("%-9.2g %-5d %8.0f %6.0f %7d %5d  %s" % (tail, cnt, mu, sd, mn, nn, key))
    lost = sum(1 for _, k in draws if k)
    p_any = 1 - math.prod(1 - r[0] for r in rows)
    print("draws with at least one constraint below 0: %d of %d; normal-tail estimate over all constraints "
          "(as if independent): %.2g" % (lost, n, p_any))


if __name__ == "__main__":
    main()
