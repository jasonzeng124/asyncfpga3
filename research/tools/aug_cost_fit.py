#!/usr/bin/env python3
"""aug_cost_fit.py BOARD_TSV NAME=RUN_LOG [NAME=RUN_LOG ...] -- the August gcd build's board latencies against the
full stack's, per vector and through gcd's per-loop cost model.

    python3 research/tools/aug_cost_fit.py research/board/aug/logs/gcd_cost.tsv \
        min=$W/min/run.log max=$W/max/run.log band=$W/band/run.log bandcell=$W/bandcell/run.log

BOARD_TSV is the board's gcd_cost.tsv (a b k ctzpre main ctzin result cycles latmin latmax; FIXED batches of 200,
FCLK0 100 MHz).  Each RUN_LOG is ps7_bench.v's output for the SAME bitstream (one FIXED batch per vector, +VECFILE);
its BENCHRES lines give latmin/latmax in aclk cycles, the same counter the board read.  Rows are paired by (a, b);
a batch that did not complete, whose result disagrees with the board's, or whose two runs disagree (the August
harness's async-latch race), is reported and left out.

Printed:
  * per vector: board latmin, each run's latmin, and x = (board - FAST_MIN) / (SLOW_MAX - FAST_MIN) when both
    corners are given (min=, max=);
  * per run and for the board: least squares latency_ns = base + k1*k + k2*ctzpre + k3*main + k4*ctzin, with the
    board table's own loop counters (the model of cells/hw/gcd_cost_fit.py), 10 ns per cycle.
"""
import math, re, sys


def lstsq(X, y):
    n = len(X[0])
    A = [[sum(r[i] * r[j] for r in X) for j in range(n)] + [sum(r[i] * v for r, v in zip(X, y))] for i in range(n)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(A[r][c]))
        A[c], A[p] = A[p], A[c]
        for r in range(n):
            if r != c and A[c][c]:
                f = A[r][c] / A[c][c]
                A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    beta = [A[i][n] / A[i][i] for i in range(n)]
    res = [v - sum(b * x for b, x in zip(beta, r)) for r, v in zip(X, y)]
    return beta, math.sqrt(sum(e * e for e in res) / max(1, len(X) - n))


RACE = {}


def main():
    board = {}
    for ln in open(sys.argv[1]).read().splitlines()[1:]:
        f = ln.split("\t")
        a, b = int(f[0]), int(f[1])
        board[(a, b)] = dict(cnt=[int(v) for v in f[2:6]], result=int(f[6]), lmin=int(f[8]), lmax=int(f[9]))
    runs = {}
    for arg in sys.argv[2:]:
        name, path = arg.split("=", 1)
        r = {}
        for ln in open(path):
            if not ln.startswith("BENCHRES"):
                continue
            d = dict(re.findall(r"(\w+)=(\S+)", ln))
            key = (int(d["op0"], 16), int(d["op1"], 16))
            ok = ln.rstrip().endswith("DONE") and int(d["completed"]) == int(d["n"])
            # the August harness reads an unsynchronised latch: a batch whose runs disagree (the bench's mismatch
            # sticky, MISM_ST bit 0) or whose latencies differ by more than 3 cycles (a stale or late capture) hit
            # that race -- its latencies are not the kernel's, so it is reported and left out of the fit
            if ok and (int(d["mism_st"], 16) & 1 or int(d["latmax"]) - int(d["latmin"]) > 3):
                RACE.setdefault(name, []).append("%d,%d lat %s-%s mism_st %s" % (int(d["op0"], 16), int(d["op1"], 16),
                                                                                 d["latmin"], d["latmax"], d["mism_st"]))
                continue
            if key in board and ok and int(d["odata"], 16) != board[key]["result"]:
                print("  %s %s: result %s != board %d -- left out" % (name, key, d["odata"], board[key]["result"]))
                ok = False
            if not ok:
                print("  %s %s: %s -- left out" % (name, key, ln.split()[-1]))
                continue
            r[key] = (int(d["latmin"]), int(d["latmax"]))
        runs[name] = r
    for name, v in RACE.items():
        print("  %s: %d batch(es) hit the harness race, left out: %s" % (name, len(v), "; ".join(v)))
    names = list(runs)
    print("%-24s %8s  %s%s" % ("a,b", "board", "  ".join("%8s" % n for n in names),
                               "   x(board)" if "min" in runs and "max" in runs else ""))
    xs = []
    for key in board:
        row = "%-24s %8d  " % ("%d,%d" % key, board[key]["lmin"])
        row += "  ".join("%8s" % (runs[n][key][0] if key in runs[n] else "-") for n in names)
        if "min" in runs and "max" in runs and key in runs["min"] and key in runs["max"]:
            lo, hi = runs["min"][key][0], runs["max"][key][0]
            if hi > lo:
                x = (board[key]["lmin"] - lo) / (hi - lo)
                xs.append((board[key]["lmin"], x))
                row += "   %.3f" % x
        print(row)
    if xs:
        big = sorted(x for l, x in xs if l >= 100)
        print("x over vectors with board latency >= 100 cycles (%d): median %.3f  range %.3f-%.3f"
              % (len(big), big[len(big) // 2], big[0], big[-1]))
    names_fit = ["base", "per k", "per ctz-pre", "per main", "per ctz-in"]
    print("cost model (ns, 10 ns per cycle):      " + "  ".join("%11s" % n for n in names_fit) + "   rms")
    for name, src in [("board", {k: (v["lmin"], v["lmax"]) for k, v in board.items()})] + list(runs.items()):
        keys = [k for k in board if k in src]
        X = [[1.0] + board[k]["cnt"] for k in keys]
        y = [10.0 * src[k][0] for k in keys]
        if len(keys) < 6:
            print("  %-10s (%d vectors: too few)" % (name, len(keys)))
            continue
        beta, rms = lstsq(X, y)
        print("  %-10s %3d vec  " % (name, len(keys)) + "  ".join("%11.1f" % b for b in beta) + "   %.1f" % rms)


if __name__ == "__main__":
    main()
