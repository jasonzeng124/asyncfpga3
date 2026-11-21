#!/usr/bin/env python3
"""loop_cost_judge.py KERNEL STEP_TSV BASE_TSV [--clk-mhz F] -- judges a "shrunk sizes vs base" board pair measured
with cells/hw/loop_cost.sh (one run on each build, OUT copied aside).

loop_cost.sh asserts a derived oracle at every point and writes a row only for a point that passed it, so a missing
row is a wrong answer or a hang on the board.

    === PASS ... ===  exit 0   both builds answered every point of KERNEL's sweep
    === FAIL ... ===  exit 1   a point is missing (the line says which build and point)

Then, for information: each build's per-iteration cost (least-squares slope of latmin on iterations, in ns at
--clk-mhz, default 83.33 = CLK_CTRL 0x00100C00) and the ratio base/step.
"""
import sys

POINTS = {"xorshift": [1, 2, 4, 8, 16, 32, 64, 128, 256], "ipow": [1, 2, 4, 6, 8, 12, 16, 20, 24, 28, 31],
          "collatz": [1, 2, 4, 6, 8, 10, 12, 14, 15], "collatz64": [1, 2, 4, 8, 12, 16, 20, 24, 28, 30]}


def load(path):
    rows = {}
    for ln in open(path).read().splitlines()[1:]:
        f = ln.split()
        if len(f) >= 2:
            rows[int(f[0])] = float(f[1])
    return rows


def slope(rows):
    xs = sorted(rows)
    n = len(xs); sx = sum(xs); sy = sum(rows[x] for x in xs)
    sxx = sum(x * x for x in xs); sxy = sum(x * rows[x] for x in xs)
    return (n * sxy - sx * sy) / (n * sxx - sx * sx)


def main():
    a = [x for x in sys.argv[1:] if not x.startswith("--")]
    mhz = 83.333
    if "--clk-mhz" in sys.argv:
        v = sys.argv[sys.argv.index("--clk-mhz") + 1]
        mhz = float(v); a.remove(v)
    k, step, base = a[0], load(a[1]), load(a[2])
    pts = POINTS[k]
    missing = [("step", p) for p in pts if p not in step] + [("base", p) for p in pts if p not in base]
    if missing:
        print("=== FAIL: %d point(s) missing (oracle failed or hung on the board): %s ===" % (len(missing), missing))
        sys.exit(1)
    print("=== PASS: %s step and base builds answered all %d points correctly ===" % (k, len(pts)))
    s, b = slope(step) * 1000.0 / mhz, slope(base) * 1000.0 / mhz
    print("  per iteration: step %.2f ns, base %.2f ns (aclk %.2f MHz); base/step %.3f" % (s, b, mhz, b / s))


if __name__ == "__main__":
    main()
