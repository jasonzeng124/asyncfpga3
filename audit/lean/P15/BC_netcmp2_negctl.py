#!/usr/bin/env python3
"""Auditor P15bc: the simulator/spec harness of BC_netcmp2.py must detect wrong specs (sanity)."""
import sys, json, random
sys.path.insert(0, sys.argv[3])
import BC_netcmp2 as B
j = json.load(open(sys.argv[1])); L = sys.argv[2]
rnd = random.Random(1)
wrong = {
 "uselect0": lambda a, b: a if a < b else b,                        # unsigned compare
 "uselect1": lambda a, b: (a - b) & B.M if a >= b else (b - a) & B.M, # unsigned absdiff
 "uori2": lambda a, b: int(a < b),                                    # unsigned compare
 "ushli0": lambda a, b: (a << (b + 1)) & B.M,
}
for u, f in wrong.items():
    _, m, inb, drv, _ = B.compare(j, L, u)
    bad = 0
    for _ in range(1000):
        a, b = rnd.getrandbits(32), rnd.getrandbits(32)
        if u == "ushli0": b %= 31
        if B.simulate(m, inb, drv, {0: a, 1: b}) != f(a, b): bad += 1
    print(u, "wrong-spec mismatches", bad, "/1000")
