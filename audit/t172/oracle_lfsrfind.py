#!/usr/bin/env python3
"""Auditor's own lfsrfind oracle (T172). No research code imported.
Semantics from kernels/lfsrfind/lfsrfind.c (read): x = seed & 0xFFFF, k = key & 0xFFFF; for i in 0..255: if x == k break;
x = (x >> 1) ^ (-(x & 1) & 0xB400); return i (256 if not found). Bench: op0 -> seed, op1 -> key, no domain mask
(cells/hw/gen_bench.py has no lfsrfind restriction). SIG = fold over runs of rotl1(sig) ^ result, from 0.
usage: oracle_lfsrfind.py mkvec OUT.hex | check VEC.hex LOG NRUNS
"""
import random, re, sys
M = 0xFFFFFFFF

def step(x): return (x >> 1) ^ ((-(x & 1)) & 0xB400)

def lf(seed, key):
    x, k = seed & 0xFFFF, key & 0xFFFF
    for i in range(256):
        if x == k: return i
        x = step(x) & 0xFFFF
    return 256

def sig(x, n):
    s = 0
    for _ in range(n): s = (((s << 1) & M) | (s >> 31)) ^ x
    return s

def mkvec(out):
    rng = random.Random(20261120); v = []
    for L in (0, 1, 2, 3, 5, 10, 31, 32, 63, 64, 100, 127, 128, 200, 254, 255, 9, 0, 33):
        s = rng.randrange(1, 1 << 16) | (rng.randrange(0, 1 << 16) << 16)   # random high half (ignored by the C)
        x = s & 0xFFFF
        for _ in range(L): x = step(x)
        v.append((s, x | (rng.randrange(0, 1 << 16) << 16)))
    v.append((0x00000001, 0x00000000))      # 0 never reached from a nonzero seed: 256
    v.append((0x00000000, 0x00000000))      # seed 0 stays 0: 0
    v.append((0x0000ace1, 0x00000000))      # not found: 256
    with open(out, "w") as f:
        for s, k in v: f.write("%08x %08x\n" % (s & M, k & M))
    print("wrote %d vectors; answers %s" % (len(v), [lf(s, k) for s, k in v]))

def check(vec, log, n):
    w = open(vec).read().split(); vecs = [(int(w[i], 16), int(w[i + 1], 16)) for i in range(0, len(w), 2)]
    rows = {}
    for ln in open(log):
        m = re.search(r"BENCHRES batch=(\d+) .*?op0=([0-9a-f]+) op1=([0-9a-f]+) n=(\d+) completed=(\d+) .*?sig=([0-9a-f]+) "
                      r"odata=([0-9a-f]+) mism_st=(\S+) ill=([0-9a-f]+) .* (DONE|HANG)\s*$", ln)
        if m: rows[int(m.group(1))] = m
    ok = 0
    for j, (s, k) in enumerate(vecs):
        e = lf(s, k); m = rows.get(j)
        if not m: print("%3d %08x %08x exp %3d MISSING" % (j, s, k, e)); continue
        good = (int(m.group(2), 16) == s and int(m.group(3), 16) == k and int(m.group(7), 16) == e and
                int(m.group(6), 16) == sig(e, n) and int(m.group(5)) == n and m.group(10) == "DONE" and int(m.group(9), 16) == 0)
        ok += good
        print("%3d %08x %08x exp %3d got %s %s %s" % (j, s, k, e, m.group(7), m.group(10), "OK" if good else "MISMATCH"))
    print("oracle agreement: %d/%d" % (ok, len(vecs))); return ok == len(vecs)

if __name__ == "__main__":
    if sys.argv[1] == "mkvec": mkvec(sys.argv[2])
    else: sys.exit(0 if check(sys.argv[2], sys.argv[3], int(sys.argv[4])) else 1)
