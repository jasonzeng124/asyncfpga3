#!/usr/bin/env python3
"""tools-B/auto/suite/ploracle.py KERNEL I0 a,b ... (shard B): the kernel's C loop (kernels/K/K.c, transcribed; 32-bit
wrap, signed i and n) started from loop counter i = I0 instead of 0, every other loop variable at its C initial value, in
the order the compiled (rotated) loop runs it: the entry test 0 < n, then body, i++, while (i < n). Prints one 8-digit hex
out0 per pair. Only for n > I0 (refuses otherwise: the rotated graph runs the body once there, the C does not)."""
import sys
M = 0xffffffff
def s32(x): x &= M; return x - (1 << 32) if x >> 31 else x
def run(k, i0, a, n):
    a &= M; n = s32(n); i = s32(i0)
    if not (n > i): sys.exit("ploracle: n must exceed I0")
    if k == "countloop":
        s = 0
        while i < n: s = ((s + (i & M)) ^ a) & M; i += 1
        return s
    if k == "horner":
        r = 0
        while i < n: r = (r * a + ((i & M) ^ 0x5a)) & M; i += 1
        return r
    if k == "brhash":
        h = a
        while i < n:
            if h & 1:
                h = (h >> 1) ^ 0xEDB88320; h = (h + (h << 4) + (i & M)) & M; h ^= h >> 13
            else:
                h = (h ^ (h << 9)) & M; h = ((h >> 2) + ((i << 1) & M)) & M; h = (h ^ (h << 5) ^ 0x2545F491) & M
            i += 1
        return h
    if k == "varshift":
        v = a; acc = 0x5bd1e995
        while i < n:
            kk = acc >> 27
            acc = ((acc << (kk & 7)) & M) ^ (v >> kk) ^ ((s32(acc) >> (31 - kk)) & M) ^ (i & M); acc &= M; i += 1
        return acc
    sys.exit("ploracle: unknown kernel " + k)
k, i0 = sys.argv[1], int(sys.argv[2], 0)
for p in sys.argv[3:]:
    a, n = (int(t, 0) for t in p.split(","))
    print("%08x" % run(k, i0, a, n))
