#!/usr/bin/env python3
"""T180 auditor's own digitsum oracle, from kernels/digitsum/digitsum.c (no research code imported):
  v = (unsigned)x; b = (unsigned)base; if b < 2: b = 10; s = 0; while v: s += v % b; v //= b; return s (u32 wrap).
digitdiv builds the same function (bdc rewrites % to v - (v / b) * b). SIG per batch = fold rotl1(sig) ^ result, from 0.
usage: oracle_digitsum.py mkvec OUT.hex | check VEC.hex LOG NRUNS"""
import re, sys
M = 0xFFFFFFFF
def ds(x, base):
    v, b = x & M, base & M
    if b < 2: b = 10
    s = 0
    while v:
        s = (s + v % b) & M; v //= b
    return s
def sig(x, n):
    s = 0
    for _ in range(n): s = (((s << 1) & M) | (s >> 31)) ^ x
    return s
OWN = [(0x7fffffff, 3), (0x80000000, 0x80000000), (12345, 1), (0xdeadbeef, 0x10), (0xfffffffe, 0xffffffff), (999999999, 10),
       (0x12345678, 7), (1, 0xffffffff)]
def mkvec(src, out):
    w = [l.split() for l in open(src) if l.strip() and not l.startswith('//')]
    v = [(int(a, 16), int(b, 16)) for a, b in w] + OWN
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
