#!/usr/bin/env python3
"""gen_vectors.py -- operand pairs and expected results for the gcd_ps GLS.

    python3 cells/gls/ps/gen_vectors.py OUT.hex [--n 24] [--seed 1]

Expected values come from bdc/simcheck.py's ref_gcd, the transcription of
Dynamatic's gcd.c (Stein's algorithm, signed i32), and are cross-checked
against math.gcd (operands are kept in [0, 2^31), where the two agree).
Nothing here is pasted from a simulation.

The vectors are chosen OUTSIDE gcd_rig.v's 16-entry table, and to reach what
that table cannot on gcd_ps's full-width operand path: bit 31's neighbour
(2^31-1), operand bits the table never set, a deep k-loop (both operands
sharing 2^20+), large coprime pairs (long subtract loop), a == b, one operand 0,
and seeded random pairs over the whole range.  Degenerate pairs whose answer
equals a failure value (0) are excluded except the two early returns, which
return a non-zero operand.

Format: one vector per line, three 8-digit hex words "a b expected", read by
cells/gls/ps/ps7_master.v with $readmemh into a flat array.
"""
import argparse, math, os, random, sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "../../.."))
from bdc.simcheck import ref_gcd  # noqa: E402

# gcd_rig.v's table (a, b), excluded
RIG = {(5, 5), (0, 7), (0, 7), (6, 0x12), (0xC, 6), (0x12, 0x30), (1, 1), (1, 1),
       (5, 0x11), (0x20, 0x12B87CA0), (0x798F20, 0x15), (0x1CE, 0x42F), (6, 0xC0),
       (0x10E, 0x1000), (0x1000, 0x10000), (0x18697, 0x18697), (0x18697, 0xC),
       (0xC0A14, 0x1E240), (1, 2), (0x7FFFFFFF, 1), (0xF423F, 0xF4240), (0xC, 0x3C),
       (0x24, 0x100), (0x300, 0x400), (7, 0)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--n", type=int, default=24)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    fixed = [
        (0x7FFFFFFF, 0x7FFFFFFE),        # top of the range, coprime neighbours
        (0x7FFFFFFF, 0x7FFFFFFF),        # a == b at the top
        (0x40000000, 0x60000000),        # k-loop 29 deep
        (0x55555555, 0x2AAAAAAA),        # alternating bits
        (2147483629, 2147483587),        # two large primes: long subtract loop
        (0, 0x6ABCDEF1),                 # early return b
        (0x3FFFFFFF, 0),                 # early return a
        (0x12345678, 0x0ABCDEF0),
        (0x0F0F0F0F * 4, 0x0F0F0F0F * 6),
        (0x00FFFFFF << 7, 0x00FFFFFE << 5),
    ]
    rng = random.Random(a.seed)
    vecs = list(fixed)
    while len(vecs) < a.n:
        x, y = rng.randrange(1, 2 ** 31), rng.randrange(1, 2 ** 31)
        if rng.random() < 0.5:           # give half of them a shared power of two
            k = rng.randrange(1, 20)
            x, y = (x << k) & 0x7FFFFFFF or 1, (y << k) & 0x7FFFFFFF or 1
        vecs.append((x, y))
    with open(a.out, "w") as f:
        for x, y in vecs[:a.n]:
            assert 0 <= x < 2 ** 31 and 0 <= y < 2 ** 31 and (x, y) not in RIG
            e = ref_gcd({"a": x, "b": y})["out0"]
            assert e == math.gcd(x, y), (x, y, e, math.gcd(x, y))
            assert e != 0
            f.write("%08x %08x %08x\n" % (x, y, e))
    print("%d vectors -> %s" % (min(a.n, len(vecs)), a.out))


if __name__ == "__main__":
    main()
