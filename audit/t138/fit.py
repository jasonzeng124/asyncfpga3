#!/usr/bin/env python3
"""T138 own fit: ns per iteration = 10 ns x least-squares slope of lmin (bench cycles at 100 MHz) on exp_steps, from
the own oracle tables (t65/oracle_collatz.py check; a row counts when odata = steps and compl = 2), vectors with lmin >= 50 cycles (as research, startup-dominated
below). Prints both corners, the band-0.288 and band-0.222 interpolations, and research's / the board's figures."""
import sys, numpy as np
def rows(p):
    out = []
    for l in open(p):
        f = l.split()
        if len(f) > 12 and f[0].isdigit() and f[4] != '-' and int(f[4], 16) == int(f[3]) and f[7] == '2': out.append((int(f[3]), int(f[9])))  # result right, both runs completed (the August bench may carry no sig)
    return out
mn, mx = rows(sys.argv[1]), rows(sys.argv[2])
s = {}
for name, r in (('FAST_MIN', mn), ('SLOW_MAX', mx)):
    r = [x for x in r if x[1] >= 50]
    X, Y = np.array([a for a, _ in r]), np.array([b for _, b in r])
    s[name] = 10 * np.polyfit(X, Y, 1)[0]; print(f"{name}: {len(r)} vectors, {s[name]:.2f} ns/iter")
for b in (0.288, 0.222):
    v = s['FAST_MIN'] + b * (s['SLOW_MAX'] - s['FAST_MIN']); print(f"band {b}: {v:.2f} ns/iter ({100*(v/92.73-1):+.1f}% vs board 92.73)")
print("research: FAST_MIN 65.16, SLOW_MAX 188.76; board 92.73 (SIM-VS-BOARD b4f2ce555); own x from board = %.3f" % ((92.73 - s['FAST_MIN']) / (s['SLOW_MAX'] - s['FAST_MIN'])))
