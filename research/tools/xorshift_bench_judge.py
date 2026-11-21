#!/usr/bin/env python3
"""xorshift_bench_judge.py S50_TSV BASE_TSV [--clk-mhz F] -- judges board list item "xorshift x0.5" (BOARD-QUEUE #6).

Inputs are two runs of cells/hw/xorshift_cost.sh (OUT=...), one on the x0.5 bench build and one on the T3 base bench
build.  xorshift_cost.sh asserts the derived oracle at each of its 17 round counts and writes a row only for a point
that passed it, so a missing row is a wrong answer (or a hang) on the board.

    === PASS ... ===   exit 0   both builds answered all 17 points correctly
    === FAIL ... ===   exit 1   a point is missing from either file (the log says which)

Then, for information (not part of the verdict): the per-round cost of each build (least-squares slope of cycles/run
on rounds, converted to ns at --clk-mhz, default 83.33 = CLK_CTRL 0x00100C00, the clock build_bench.sh closes timing
for; the kernel is asynchronous, so its per-round time does not depend on the harness clock), their ratio, and where x0.5's slope sits between the full stack's corners on the same bench
top (research/data/xorshift_bench/results.tsv, simulated at 100 MHz and converted to ns;
the August kernels sat at x = 0.21-0.23 of that span, research/data/aug_kernels).  Predicted ratio base/x0.5:
1.28-1.52, mean 1.43-1.45 by corner (8 routes x 3 corners, paired by seed; the board builds seed 1: 1.47-1.49).
"""
import sys

POINTS = [0, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256]
CORNER = {"s50": (26.60, 30.21, 74.74, 83.64), "base": (38.66, 41.27, 108.34, 117.11)}  # ns/round: min lo/hi, max lo/hi


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
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    mhz = float(sys.argv[sys.argv.index("--clk-mhz") + 1]) if "--clk-mhz" in sys.argv else 83.333
    if "--clk-mhz" in sys.argv:
        args.remove(sys.argv[sys.argv.index("--clk-mhz") + 1])
    s50, base = load(args[0]), load(args[1])
    missing = [("x0.5", p) for p in POINTS if p not in s50] + [("T3", p) for p in POINTS if p not in base]
    if missing:
        print("=== FAIL: %d point(s) missing (oracle failed or hung on the board): %s ===" % (len(missing), missing))
        sys.exit(1)
    print("=== PASS: x0.5 and T3 bench builds answered all %d round counts correctly ===" % len(POINTS))
    a, b = slope(s50) * 1000.0 / mhz, slope(base) * 1000.0 / mhz      # cycles -> ns
    for name, v, key in (("x0.5", a, "s50"), ("T3", b, "base")):
        lo, _, _, hi = CORNER[key]
        x = (v - CORNER[key][0]) / (CORNER[key][3] - CORNER[key][0])
        print("  %-5s per round %.2f ns (aclk %.2f MHz); full stack %.2f-%.2f ns; x = %.3f of that span" %
              (name, v, mhz, lo, hi, x))
    print("  speedup T3/x0.5 per round: %.3f (full stack: 1.28-1.52 over 8 routes, 1.47-1.49 on seed 1)" % (b / a))


if __name__ == "__main__":
    main()
