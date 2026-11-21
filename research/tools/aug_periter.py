#!/usr/bin/env python3
"""aug_periter.py -- ns per iteration of the August bench builds (research/data/aug_kernels), board against the full
stack: a least-squares slope of latency (10 ns aclk cycles) on the iteration count, per kernel, for the board, FAST_MIN,
SLOW_MAX and the interpolations at band 0.288 (ring128) and 0.222 (the kernels' own fit). Iterations from the C:
collatz / collatz64 = the result (steps); ipow = bit length of e. Vectors under 50 board cycles are left out for collatz*
(startup-dominated), as in aug_x.py. The interpolation assumes latency is linear in the band, which aug_x.py's per-vector
x spread (~0.01) supports."""
import os, numpy as np
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../data/aug_kernels")
def load(k):
    B = {}
    for l in list(open(f"{D}/{k}_bench_gen_board.tsv"))[1:]:
        p = l.split("\t"); B[(p[0], p[1])] = p[4]
    rows = []
    for l in open(f"{D}/{k}_bench_gen_x.txt"):
        p = l.split()
        if len(p) != 5 or "," not in p[0]: continue
        try: bd, mn, mx = float(p[1]), float(p[2]), float(p[3])
        except ValueError: continue
        a, b = p[0].split(","); rows.append((a, b, bd, mn, mx, B.get((a, b))))
    return rows
print("kernel | vectors | board | FAST_MIN | SLOW_MAX | band 0.288 (error) | band 0.222 (error)")
for k in ["collatz", "collatz64", "ipow"]:
    X, Y = [], []
    for a, b, bd, mn, mx, od in load(k):
        it = int(od) if k.startswith("collatz") else int(b).bit_length()
        if k.startswith("collatz") and bd < 50: continue
        X.append(it); Y.append((bd, mn, mx))
    X, Y = np.array(X), np.array(Y)
    cols = [Y[:, 0], Y[:, 1], Y[:, 2], Y[:, 1] + 0.288 * (Y[:, 2] - Y[:, 1]), Y[:, 1] + 0.222 * (Y[:, 2] - Y[:, 1])]
    s = [10 * np.polyfit(X, c, 1)[0] for c in cols]
    print(f"{k} | {len(X)} | {s[0]:.2f} | {s[1]:.2f} | {s[2]:.2f} | {s[3]:.2f} ({100*(s[3]/s[0]-1):+.1f}%) | {s[4]:.2f} ({100*(s[4]/s[0]-1):+.1f}%)")
