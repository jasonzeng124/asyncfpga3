#!/usr/bin/env python3
"""T186 auditor's own quadrec oracle, from kernels/quadrec/quadrec.c (no research code imported):
  a=x, b=0x6a09e667, c=0xbb67ae85, d=0x3c6ef372; n times (signed n, n<=0: none): t=a+(b^c)+(d>>3); a,b,c,d=b,c,d,t;
  return a ^ (b<<1) ^ (c<<2) ^ (d<<3) (u32). SIG per batch = fold rotl1(sig) ^ result, from 0.
usage: oracle_quadrec.py mkvec OUT.hex | check VEC.hex LOG NRUNS"""
import re, sys
M = 0xFFFFFFFF
def ds(x, n):
    n = n - (1 << 32) if n & 0x80000000 else n
    a, b, c, d = x & M, 0x6a09e667, 0xbb67ae85, 0x3c6ef372
    for _ in range(max(n, 0)):
        t = (a + (b ^ c) + (d >> 3)) & M
        a, b, c, d = b, c, d, t
    return (a ^ (b << 1) ^ (c << 2) ^ (d << 3)) & M
def sig(x, n):
    s = 0
    for _ in range(n): s = (((s << 1) & M) | (s >> 31)) ^ x
    return s
OWN = [(0, 0), (0x7fffffff, 1), (0x80000000, 2), (0xffffffff, 3), (12345, 4), (0xdeadbeef, 5), (0x12345678, 7),
       (1, 0xffffffff), (0x80000000, 0x80000000), (0xcafef00d, 31), (0x0badc0de, 64), (42, 50), (0x55aa55aa, 200),
       (0xfffffffe, 255), (0x31415926, 256)]
def mkvec(src, out):
    v = OWN
    open(out, 'w').write(''.join('%08x %08x\n' % p for p in v)); print(len(v), 'vectors')
def check(vec, log, n):
    w = open(vec).read().split(); vecs = [(int(w[i], 16), int(w[i+1], 16)) for i in range(0, len(w), 2)]
    rows = {}
    for ln in open(log):
        m = re.search(r"BENCHRES batch=(\d+) .*?op0=([0-9a-f]+) op1=([0-9a-f]+) n=(\d+) completed=(\d+) cycles=(\d+) .*?"
                      r"sig=([0-9a-f]+) odata=([0-9a-f]+) .*?ill=([0-9a-f]+) .* (DONE|HANG)\s*$", ln)
        if m: rows[int(m.group(1))] = m
    ok = 0
    for j, (a, b) in enumerate(vecs):
        e = ds(a, b); m = rows.get(j)
        g = bool(m) and int(m.group(2), 16) == a and int(m.group(3), 16) == b and int(m.group(8), 16) == e and \
            int(m.group(7), 16) == sig(e, n) and int(m.group(5)) == n and m.group(10) == 'DONE' and int(m.group(9), 16) == 0
        ok += g
        print('%2d %08x %08x exp %08x got %s %s' % (j, a, b, e, m.group(8) if m else 'MISSING', 'OK' if g else 'MISMATCH'))
    print('oracle agreement: %d/%d' % (ok, len(vecs))); return ok == len(vecs)
if __name__ == '__main__':
    if sys.argv[1] == 'mkvec': mkvec(sys.argv[2], sys.argv[3])
    else: sys.exit(0 if check(sys.argv[2], sys.argv[3], int(sys.argv[4])) else 1)
