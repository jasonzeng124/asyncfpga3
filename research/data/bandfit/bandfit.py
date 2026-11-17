#!/usr/bin/env python3
"""bandfit.py KERNEL X0 LOG [LOG ...] -- research/data/bandfit: ns per iteration of one August bench build at
(x = LUT + interconnect band, y = CARRY4 / SELMUX2_1 / SLICE_FFX band), against the board.

Each LOG is run1.sh's (ps7_bench.v BENCHRES lines, FCLK 100 MHz, at band X0 with its own y in the header).
Board latmin / odata: research/data/aug_kernels/KERNEL_bench_gen_board.tsv (aug_board_vectors.py, from the logs).
FAST_MIN / SLOW_MAX per vector: research/data/aug_kernels/KERNEL_bench_gen_{min,max}.log (same build, same harness).
Iterations from the C: collatz / collatz64 = the result (steps), ipow = bit length of e.
ns/iter = 10 ns x least-squares slope of latmin on iterations.  Refitted x at that y: x0 + (board - sim) / (max - min)
on the slopes (latency is linear in the band: aug_x.py's per-vector spread ~0.01); per vector the same, median.
Every simulated result is checked against the board's (wrong -> listed, row left out)."""
import os, re, sys
import numpy as np
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "aug_kernels")


def bench(path):
    out = {}
    for ln in open(path):
        if ln.startswith("BENCHRES"):
            d = dict(re.findall(r"(\w+)=(\S+)", ln))
            out[(int(d["op0"], 16), int(d["op1"], 16))] = d
    return out


def iters(k, a, b, od):
    return od if k.startswith("collatz") else b.bit_length()


def main():
    k, x0, logs = sys.argv[1], float(sys.argv[2]), sys.argv[3:]
    board = {}
    for ln in list(open(f"{D}/{k}_bench_gen_board.tsv"))[1:]:
        f = ln.split("\t"); board[(int(f[0]), int(f[1]))] = (int(f[2]), int(f[4]))
    mn, mx = bench(f"{D}/{k}_bench_gen_min.log"), bench(f"{D}/{k}_bench_gen_max.log")
    for lg in logs:
        hdr = open(lg).readline().strip()
        y = re.search(r"y=(\S+)", hdr).group(1)
        r = bench(lg); bad = []; X = []; Y = []
        for v, d in sorted(r.items(), key=lambda t: board[t[0]][0]):
            bl, bo = board[v]
            ok = d["completed"] == d["n"] and int(d["odata"], 16) == bo & 0xFFFFFFFF and not int(d["mism_st"], 16) & 1
            if not ok:
                bad.append("%s odata %s board %d completed %s/%s mism_st %s" % (v, d["odata"], bo, d["completed"], d["n"], d["mism_st"]))
                continue
            X.append((iters(k, *v, bo), bl, int(d["latmin"]),
                      int(mn[v]["latmin"]) if v in mn else None, int(mx[v]["latmin"]) if v in mx else None))
        it = np.array([t[0] for t in X], float)
        sb = 10 * np.polyfit(it, [t[1] for t in X], 1)[0]; ss = 10 * np.polyfit(it, [t[2] for t in X], 1)[0]
        full = [t for t in X if t[3] is not None and t[4] is not None]
        ia = np.array([t[0] for t in full], float)
        smin = 10 * np.polyfit(ia, [t[3] for t in full], 1)[0]; smax = 10 * np.polyfit(ia, [t[4] for t in full], 1)[0]
        sb_f = 10 * np.polyfit(ia, [t[1] for t in full], 1)[0]; ss_f = 10 * np.polyfit(ia, [t[2] for t in full], 1)[0]
        xs = x0 + (sb_f - ss_f) / (smax - smin)
        xv = [x0 + (t[1] - t[2]) / (t[4] - t[3]) for t in full if t[1] >= 50]
        print("%s y=%s vectors %d ok %d wrong %d | ns/iter board %.2f sim %.2f (%+.2f%%) | refit x: slope %.4f, "
              "per-vector median %.4f (%.4f-%.4f, %d vec >= 50 cyc; slope on %d vec with both corners)" % (
                  k, y, len(r), len(X), len(bad), sb, ss, 100 * (ss / sb - 1), xs,
                  np.median(xv) if xv else float("nan"), min(xv) if xv else 0, max(xv) if xv else 0, len(xv), len(full)))
        print("   iters/board/sim:", " ".join("%d:%d/%d" % t[:3] for t in X))
        for b in bad:
            print("   WRONG", b)
        summ = re.search(r"BENCHSUMMARY.*", open(lg).read())
        print("   ", summ.group(0) if summ else "NO BENCHSUMMARY (run cut?)")


main()
