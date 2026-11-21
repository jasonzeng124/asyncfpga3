#!/usr/bin/env python3
"""aug_x.py BOARD_TSV MIN_LOG MAX_LOG [NAME=LOG ...] -- where a kernel's board latency sits between the full stack's
corners, per vector, for one August bench build.

    python3 research/tools/aug_x.py $S/aug/v_ipow_bench_gen.tsv $W/min/run.log $W/max/run.log

BOARD_TSV is research/tools/aug_board_vectors.py's (op0 op1 latmin latmax odata log); the logs are ps7_bench.v's
(+VECFILE of the same vectors, FIXED mode) on the SAME bitstream at FAST_MIN and SLOW_MAX.  x = (board latmin -
FAST_MIN) / (SLOW_MAX - FAST_MIN); also given as a single latency-weighted fit over every vector.  Rows are paired by
(op0, op1); a batch that did not complete, returned another result than the board, or whose two runs differ by more
than 3 cycles or set the mismatch sticky (the August harness's latch race), is listed and left out.
"""
import re, sys


def read(path, board):
    out, bad = {}, []
    for ln in open(path):
        if not ln.startswith("BENCHRES"):
            continue
        d = dict(re.findall(r"(\w+)=(\S+)", ln))
        k = (int(d["op0"], 16), int(d["op1"], 16))
        if k not in board:
            continue
        why = None
        if not ln.rstrip().endswith("DONE") or int(d["completed"]) != int(d["n"]):
            why = "did not complete"
        elif int(d["odata"], 16) != board[k][2] & 0xFFFFFFFF:
            why = "result %s, board %d" % (d["odata"], board[k][2])
        elif int(d["mism_st"], 16) & 1 or int(d["latmax"]) - int(d["latmin"]) > 3:
            why = "runs disagree (lat %s-%s, mism_st %s)" % (d["latmin"], d["latmax"], d["mism_st"])
        if why:
            bad.append("%s %s" % (k, why))
        else:
            out[k] = int(d["latmin"])
    return out, bad


def main():
    board = {}
    for ln in open(sys.argv[1]).read().splitlines()[1:]:
        f = ln.split("\t")
        board[(int(f[0]), int(f[1]))] = (int(f[2]), int(f[3]), int(f[4]))
    lo, blo = read(sys.argv[2], board)
    hi, bhi = read(sys.argv[3], board)
    extra = [(a.split("=", 1)[0], read(a.split("=", 1)[1], board)) for a in sys.argv[4:]]
    for n, b in (("FAST_MIN", blo), ("SLOW_MAX", bhi)) + tuple((n, r[1]) for n, r in extra):
        for e in b:
            print("  %s left out: %s" % (n, e))
    print("%-22s %7s %7s %7s %s  %s" % ("op0,op1", "board", "min", "max", "".join("%8s" % n for n, _ in extra), "x"))
    xs, num, den = [], 0.0, 0.0
    for k in sorted(board, key=lambda k: board[k][0]):
        row = "%-22s %7d %7s %7s %s" % ("%d,%d" % k, board[k][0], lo.get(k, "-"), hi.get(k, "-"),
                                        "".join("%8s" % r[0].get(k, "-") for _, r in extra))
        if k in lo and k in hi and hi[k] > lo[k]:
            x = (board[k][0] - lo[k]) / (hi[k] - lo[k])
            row += "  %.3f" % x
            if board[k][0] >= 50:
                xs.append(x)
            num += (board[k][0] - lo[k]) * (hi[k] - lo[k]); den += (hi[k] - lo[k]) ** 2
        print(row)
    if xs:
        xs.sort()
        print("x over vectors with board latency >= 50 cycles (%d): median %.3f  range %.3f-%.3f;  weighted fit %.3f"
              % (len(xs), xs[len(xs) // 2], xs[0], xs[-1], num / den if den else float("nan")))


if __name__ == "__main__":
    main()
