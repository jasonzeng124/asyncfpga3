#!/usr/bin/env python3
"""T140 own fit (generalises t138/fit.py): ns per iteration = 10 ns x least-squares slope of lmin (100 MHz bench
cycles) on the iteration count, from own oracle tables. usage: fit2.py collatz64|ipow FASTMIN_TABLE SLOWMAX_TABLE BOARD
RESEARCH_FM RESEARCH_SM. A row counts when the result is right and both runs completed. collatz64: iterations =
exp_steps (col 3), result col 4 = steps, lmin col 9, vectors >= 50 cycles (as research); ipow: iterations = the
oracle's iters (col 3; loop trips = bit length of e), result col 5 = col 4, compl col 8, lmin col 10, all vectors."""
import sys, numpy as np
kind, fa, fb, board, rfm, rsm = sys.argv[1], sys.argv[2], sys.argv[3], float(sys.argv[4]), sys.argv[5], sys.argv[6]
def rows(p):
    out = []
    for l in open(p):
        f = l.split()
        if not (len(f) > 12 and f[0].isdigit()): continue
        try:
            if kind == 'ipow':
                if f[5] == f[4] and f[8] == '2': out.append((int(f[3]), int(f[10])))
            elif int(f[4], 16) == int(f[3]) and f[7] == '2' and int(f[9]) >= 50: out.append((int(f[3]), int(f[9])))
        except ValueError: pass
    return out
s = {}
for name, p in (('FAST_MIN', fa), ('SLOW_MAX', fb)):
    r = rows(p); X, Y = np.array([a for a, _ in r]), np.array([b for _, b in r])
    s[name] = 10 * np.polyfit(X, Y, 1)[0]; print(f"{name}: {len(r)} vectors, {s[name]:.2f} ns/iter")
for b in (0.288, 0.222):
    v = s['FAST_MIN'] + b * (s['SLOW_MAX'] - s['FAST_MIN']); print(f"band {b}: {v:.2f} ns/iter ({100*(v/board-1):+.1f}% vs board {board})")
print(f"research: FAST_MIN {rfm}, SLOW_MAX {rsm}; board {board}; own x from board = {(board - s['FAST_MIN']) / (s['SLOW_MAX'] - s['FAST_MIN']):.3f}")
