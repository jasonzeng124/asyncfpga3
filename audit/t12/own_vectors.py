#!/usr/bin/env python3
"""own_vectors.py (audit T12): the auditor's own gcd_ps GLS vectors, "a b expected" hex, expected = math.gcd.
Random pairs from the auditor's seed over [0, 2^31) plus edge cases; none taken from research's gen_vectors."""
import math, random, sys
r = random.Random(20261102)
V = [(0x7FFFFFFF, 0x7FFFFFFE), (0x7FFFFFFF, 0x7FFFFFFF), (0x40000000, 0x60000000), (12345, 0), (0, 67890),
     (2**30 + 2**20, 2**21 * 3), (2147483629, 2147483587)]          # last: two large primes
while len(V) < 24:
    a, b = r.randrange(1, 2**31), r.randrange(1, 2**31)
    if r.random() < 0.3:
        g = r.randrange(1, 2**12); a, b = (a // g) * g or g, (b // g) * g or g
    V.append((a, b))
with open(sys.argv[1], "w") as f:
    for a, b in V:
        f.write("%08x %08x %08x\n" % (a, b, math.gcd(a, b)))
