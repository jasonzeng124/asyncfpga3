#!/usr/bin/env python3
"""table.py -- research/SIM-VS-BOARD.md's ns-per-iteration table: per August kernel, the board against the full stack
(netlist decoded from the measured .bit, prjxray SDF, GLS_MODEL=fid, ps7_bench.v at 100 MHz, the board's own vectors).

Per kernel one metric, as the earlier tools defined it:
  collatz / collatz64 / ipow  ns per iteration = 10 ns x least-squares slope of latmin on iterations (aug_periter.py:
                              collatz* iterations = steps, vectors with board latency >= 50 cycles; ipow = bit length
                              of e), on the vectors that have both corners (research/data/aug_kernels/*_x.txt);
  gcd                         ns per main-loop iteration, from the least-squares cost model base + k + ctz-pre +
                              main + ctz-in on the board table's loop counters (aug_cost_fit.py), 24 vectors;
                              its upper point is band 0.288 (all 24 complete; at SLOW_MAX 10 hit the harness race);
  isprime                     n = 97 minus n = 2, ns (the only long vector with both corners; formal's A14 metric).
x = where the board's metric sits between FAST_MIN (0) and SLOW_MAX (1), every arc at one band (linear in the band:
per-vector spread ~0.01, aug_x.py; checked by the direct runs below).  x_loo = mean x of the OTHER four kernels: the
metric predicted at x_loo is an out-of-sample prediction for that kernel.  "gcd long pair" is formal's A14 gcd metric,
printed for the side-by-side; it is not a sixth kernel (x statistics use the five main rows).  [0.20, 0.31] is research's draw range
for delay chains and the rest (SIM-VS-BOARD row 1).
Direct runs (run1.sh at the kernel's own x, CARRY4 / F7F8 / FF at y) are read from logs/ when present."""
import os, re, sys
import numpy as np
H = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(H, "..", "aug_kernels")
G = os.path.join(H, "..", "aug_gcd")
GB = os.path.join(H, "..", "..", "board", "aug", "logs", "gcd_cost.tsv")


def xtxt(k):
    """(op0, op1) -> (board, min, max) from aug_x.py's table"""
    rows = {}
    for ln in open(f"{D}/{k}_bench_gen_x.txt"):
        p = ln.split()
        if len(p) == 5 and "," in p[0]:
            try:
                rows[tuple(int(v) for v in p[0].split(","))] = (float(p[1]), float(p[2]), float(p[3]))
            except ValueError:
                pass
    return rows


def odata(k):
    return {(int(f[0]), int(f[1])): int(f[4]) for f in (ln.split("\t") for ln in list(open(f"{D}/{k}_bench_gen_board.tsv"))[1:])}


def slope_kernel(k):
    od = odata(k); X, Y = [], []
    for v, (b, mn, mx) in xtxt(k).items():
        if k.startswith("collatz") and b < 50:
            continue
        X.append(od[v] if k.startswith("collatz") else v[1].bit_length()); Y.append((b, mn, mx))
    X, Y = np.array(X, float), np.array(Y)
    return len(X), [10 * np.polyfit(X, Y[:, i], 1)[0] for i in range(3)]


def bench(path):
    out = {}
    for ln in open(path):
        if ln.startswith("BENCHRES") and ln.rstrip().endswith("DONE"):
            d = dict(re.findall(r"(\w+)=(\S+)", ln))
            out[(int(d["op0"], 16), int(d["op1"], 16))] = d
    return out


def gcd_main(logs):
    """ns per main-loop iteration: board and each log, on the vectors every one of them completed right"""
    board = {}
    for ln in open(GB).read().splitlines()[1:]:
        f = ln.split("\t")
        board[(int(f[0]), int(f[1]))] = ([int(v) for v in f[2:6]], int(f[6]), int(f[8]))
    runs = [bench(p) for p in logs]
    keys = [v for v in board if all(v in r and int(r[v]["odata"], 16) == board[v][1] and not int(r[v]["mism_st"], 16) & 1
                                    and int(r[v]["latmax"]) - int(r[v]["latmin"]) <= 3 for r in runs)]
    A = np.array([[1.0] + board[v][0] for v in keys])
    out = [np.linalg.lstsq(A, [10.0 * board[v][2] for v in keys], rcond=None)[0][3]]
    for r in runs:
        out.append(np.linalg.lstsq(A, [10.0 * int(r[v]["latmin"]) for v in keys], rcond=None)[0][3])
    return len(keys), out


def main():
    K = {}
    for k in ("collatz", "collatz64", "ipow"):
        n, (b, mn, mx) = slope_kernel(k)
        K[k] = dict(metric="ns/iter", n=n, board=b, lo=mn, hi=mx, xhi=1.0)
    n, (b, mn, b288) = gcd_main([f"{G}/gcd_bench_gen_aug_min.log", f"{G}/gcd_bench_gen_aug_band0288.log"])
    K["gcd"] = dict(metric="ns/main iter", n=n, board=b, lo=mn, hi=b288, xhi=0.288)
    lp = [bench(f) for f in (f"{G}/gcd_bench_gen_aug_min.log", f"{G}/gcd_bench_gen_aug_band0288.log")]
    bl = {(int(f[0]), int(f[1])): int(f[8]) for f in (ln.split("\t") for ln in open(GB).read().splitlines()[1:])}
    A, B = (2147483647, 2147483646), (1, 1)
    K["gcd long pair"] = dict(metric="ns, (2^31-1, 2^31-2) - (1, 1)", n=2, board=10.0 * (bl[A] - bl[B]),
                              lo=10.0 * (int(lp[0][A]["latmin"]) - int(lp[0][B]["latmin"])),
                              hi=10.0 * (int(lp[1][A]["latmin"]) - int(lp[1][B]["latmin"])), xhi=0.288, aux=True)
    r = xtxt("isprime"); b, mn, mx = [10 * (r[(97, 0)][i] - r[(2, 0)][i]) for i in range(3)]
    K["isprime"] = dict(metric="ns, n 97 - n 2", n=2, board=b, lo=mn, hi=mx, xhi=1.0)
    for k, d in K.items():
        d["x"] = d["xhi"] * (d["board"] - d["lo"]) / (d["hi"] - d["lo"])
        d["at"] = lambda x, d=d: d["lo"] + x / d["xhi"] * (d["hi"] - d["lo"])
    main5 = {k: d for k, d in K.items() if not d.get("aux")}
    xs = np.array([d["x"] for d in main5.values()])
    print("| kernel | metric | vectors | board | FAST_MIN | SLOW_MAX | x (board) | x_loo | at x_loo | at 0.288 | "
          "draw range x 0.20-0.31 |")
    print("|---|---|---|---|---|---|---|---|---|---|---|")
    for k, d in K.items():
        loo = np.mean([e["x"] for kk, e in main5.items() if kk != k and not (k.startswith("gcd") and kk.startswith("gcd"))])
        p, q = d["at"](loo), d["at"](0.288)
        hi = d["hi"] if d["xhi"] == 1.0 else d["at"](1.0)
        print("| %s | %s | %d | %.2f | %.2f | %.2f%s | %.4f | %.4f | %.2f (%+.1f%%) | %.2f (%+.1f%%) | %.2f-%.2f |" % (
            k, d["metric"], d["n"], d["board"], d["lo"], hi, "" if d["xhi"] == 1.0 else " (from 0.288)", d["x"], loo,
            p, 100 * (p / d["board"] - 1), q, 100 * (q / d["board"] - 1), d["at"](0.20), d["at"](0.31)))
    print("x over the five kernels: mean %.4f, sd %.4f, range %.4f-%.4f" % (xs.mean(), xs.std(ddof=1), xs.min(), xs.max()))
    for f in sys.argv[1:]:
        print(f)


if __name__ == "__main__":
    main()
