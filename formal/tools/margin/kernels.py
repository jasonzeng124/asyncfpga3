#!/usr/bin/env python3
"""margin/kernels.py (shard C, UNTRUSTED): expected out0 values of the kernels in kernels/*.c, for the margin tool's
result check. Derived from the C source (CLAUDE.md: never from what a run printed). Integer semantics as the
handshake MLIR's i32 ops: two's-complement wrap-around, arithmetic shift right on the signed int. collatz64 is the
same C with a 64-bit datapath (the operand sign-extended). Loops are capped: a vector whose reference does not
terminate within CAP steps is refused (choose terminating vectors).
usage: kernels.py KERNEL V1 V2 ...   (V = "a,b" for gcd/xorshift, "n" for collatz/collatz64) -> prints want list"""
import sys
CAP = 1 << 20
def s32(x): x &= 0xffffffff; return x - (1 << 32) if x >> 31 else x
def s64(x): x &= (1 << 64) - 1; return x - (1 << 64) if x >> 63 else x
def gcd(a, b):
    import math; return math.gcd(a, b)
def collatz(n, w=32):
    s = s32 if w == 32 else s64
    n = s(n); steps = 0
    while n != 1:
        n = s(n >> 1) if (n & 1) == 0 else s(3 * n + 1)
        steps = s32(steps + 1)
        if steps > CAP: raise ValueError("collatz(%d) does not terminate within %d steps" % (n, CAP))
    return steps & 0xffffffff
def xorshift(seed, rounds):
    x = seed & 0xffffffff; i = 0; rounds = s32(rounds)
    while i < rounds:
        x ^= (x << 13) & 0xffffffff; x ^= x >> 17; x ^= (x << 5) & 0xffffffff; i += 1
    return x
def want(kernel, vecs):
    out = []
    for v in vecs:
        p = [int(t, 0) for t in v.split(",")]
        if kernel == "gcd": out.append(gcd(*p))
        elif kernel == "collatz": out.append(collatz(p[0]))
        elif kernel == "collatz64": out.append(collatz(p[0], 64))
        elif kernel == "xorshift": out.append(xorshift(*p))
        else: raise SystemExit("unknown kernel " + kernel)
    return out
if __name__ == "__main__":
    print(",".join(str(x) for x in want(sys.argv[1], sys.argv[2:])))
