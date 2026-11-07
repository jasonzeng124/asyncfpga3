#!/usr/bin/env python3
"""xorshift_bench_judge.py S50_TSV BASE_TSV -- judges board list item "xorshift x0.5" (BOARD-QUEUE #6).

Inputs are two runs of cells/hw/xorshift_cost.sh (OUT=...), one on the x0.5 bench build and one on the T3 base bench
build.  xorshift_cost.sh asserts the derived oracle at each of its 17 round counts and writes a row only for a point
that passed it, so a missing row is a wrong answer (or a hang) on the board.

    === PASS ... ===   exit 0   both builds answered all 17 points correctly
    === FAIL ... ===   exit 1   a point is missing from either file (the log says which)

Then, for information (not part of the verdict): the per-round cost of each build (least-squares slope of cycles/run
on rounds, aclk cycles), their ratio, and where x0.5's slope sits between the full stack's corners on the same bench
top (research/data/xorshift_bench/results.tsv: FAST_MIN 2.68-2.80, SLOW_MAX 7.48-7.82 cycles/round over 4 routes;
the August kernels sat at x = 0.21-0.23 of that span, research/data/aug_kernels).  Predicted ratio base/x0.5:
1.46-1.52 (12 paired corner runs).
"""
import sys

POINTS = [0, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256]
CORNER = {"s50": (2.680, 2.797, 7.475, 7.819), "base": (3.960, 4.128, 11.056, 11.711)}  # min lo/hi, max lo/hi


def load(path):
    rows = {}
    for ln in open(path).read().splitlines()[1:]:
        f = ln.split()
        if len(f) >= 2:
            rows[int(f[0])] = float(f[1]) / 200.0          # batch of 200 runs -> cycles per run
    return rows


def slope(rows):
    xs = sorted(rows)
    n = len(xs); sx = sum(xs); sy = sum(rows[x] for x in xs)
    sxx = sum(x * x for x in xs); sxy = sum(x * rows[x] for x in xs)
    return (n * sxy - sx * sy) / (n * sxx - sx * sx)


def main():
    s50, base = load(sys.argv[1]), load(sys.argv[2])
    missing = [("x0.5", p) for p in POINTS if p not in s50] + [("T3", p) for p in POINTS if p not in base]
    if missing:
        print("=== FAIL: %d point(s) missing (oracle failed or hung on the board): %s ===" % (len(missing), missing))
        sys.exit(1)
    print("=== PASS: x0.5 and T3 bench builds answered all %d round counts correctly ===" % len(POINTS))
    a, b = slope(s50), slope(base)
    for name, v, key in (("x0.5", a, "s50"), ("T3", b, "base")):
        lo, _, _, hi = CORNER[key]
        x = (v - CORNER[key][0]) / (CORNER[key][3] - CORNER[key][0])
        print("  %-5s per round %.3f cycles (%.1f ns at 100 MHz); full stack %.2f-%.2f; x = %.3f of that span" %
              (name, v, v * 10, lo, hi, x))
    print("  speedup T3/x0.5 per round: %.3f (full stack predicted 1.46-1.52)" % (b / a))


if __name__ == "__main__":
    main()
