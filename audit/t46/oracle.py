#!/usr/bin/env python3
"""Auditor's own ipow oracle (T46). No research code imported.

Kernel semantics, read from /root/wt-r35/cloud/fixtures/frontend/ipow/comp/cf.mlir:
  ipow(arg0:i32 b, arg1:i32 e) -> i32
    if !(e >s 0): return 1                         (signed compare; e<=0, incl. negative e, returns 1)
    r = 1; loop: if (e & 1) r = r*b; b = b*b; e = e >>s 1 (arithmetic); continue while e >s 0
    every muli is i32, i.e. wraps mod 2^32 (only the low 32 bits of each product are kept)
  (result bits are identical whether products are taken signed or unsigned mod 2^32)
Bench (cells/hw/gen_bench.py, read not imported): op0 -> arg0, op1 -> arg1, no domain mask for ipow;
SIG per batch: sig = 0, then per run sig = rotl1(sig) ^ result; ODATA = the result.

usage: oracle.py mkvec OUT.hex           -- 17 vectors (op0 op1 per line)
       oracle.py check VEC.hex LOG NRUNS -- compare every BENCHRES line with the oracle
"""
import re, sys

M = 0xFFFFFFFF


def sx(v):
    v &= M
    return v - (1 << 32) if v >> 31 else v


def ipow(b, e):
    b, e = b & M, sx(e)
    r = 1
    if not e > 0:
        return r
    iters = 0
    while True:
        if e & 1:
            r = (r * b) & M
        b = (b * b) & M
        e >>= 1                     # python >> on a signed int is arithmetic
        iters += 1
        if not e > 0:
            return r


def iters_of(e):
    e = sx(e); n = 0
    while e > 0:
        e >>= 1; n += 1
    return n


def sig(x, nruns):
    s = 0
    for _ in range(nruns):
        s = (((s << 1) & M) | (s >> 31)) ^ x
    return s


def vectors():
    # loop_cost.sh's ipow points: b=3, e=2^i-1 for i in its POINTS (11 points, i<=31) ...
    v = [(3, (1 << i) - 1) for i in (1, 2, 4, 6, 8, 12, 16, 20, 24, 28, 31)]
    # ... + 6 hand vectors: bdc/simcheck.py VECTORS["ipow"] minus (3,1),(3,7) which duplicate loop_cost
    # points (reconstruction: research's 17-vector file is not committed).
    v += [(3, 0), (2, 10), (-2, 3), (-3, 4), (7, 11), (5, 14)]
    return v


def selftest():
    # independent cross-check with python's pow for e >= 0, and hand values
    for b, e in vectors() + [(65536, 2), (-1, 31), (0, 5), (5, -3)]:
        want = pow(b, e, 1 << 32) if e > 0 else 1
        assert ipow(b, e) == want, (b, e)
    assert ipow(2, 10) == 1024 and ipow(-2, 3) == (-8) & M and ipow(-3, 4) == 81
    assert ipow(7, 11) == 1977326743 and ipow(65536, 2) == 0 and ipow(5, 14) == (6103515625 & M)
    assert iters_of(0x7fffffff) == 31 and iters_of(1) == 1 and iters_of(0) == 0


def mkvec(out):
    with open(out, "w") as f:
        for b, e in vectors():
            f.write("%08x %08x\n" % (b & M, e & M))
    print("wrote %d vectors to %s" % (len(vectors()), out))


def check(vec, log, nruns):
    words = open(vec).read().split()
    vecs = [(int(words[i], 16), int(words[i + 1], 16)) for i in range(0, len(words), 2)]
    rows = {}
    for ln in open(log):
        m = re.search(r"BENCHRES batch=(\d+) fclk_ps=(\d+) .*?op0=([0-9a-f]+) op1=([0-9a-f]+) n=(\d+) completed=(\d+) "
                      r"cycles=(\d+) .*?latmin=(\d+) latmax=(\d+) sig=([0-9a-f]+) odata=([0-9a-f]+) mism_st=(\S+) "
                      r"ill=([0-9a-f]+) .* (DONE|HANG)\s*$", ln)
        if m:
            rows[int(m.group(1))] = m
    ok = 0
    print("vec  op0       op1       iters exp_odata  sim_odata  exp_sig    sim_sig    compl cycles lmin lmax ill      fclk  state verdict")
    for j, (b, e) in enumerate(vecs):
        x = ipow(b, e); es = sig(x, nruns)
        m = rows.get(j)
        if not m:
            print("%3d  %08x %08x MISSING" % (j, b, e)); continue
        good = (int(m.group(3), 16) == b and int(m.group(4), 16) == e and int(m.group(11), 16) == x
                and int(m.group(10), 16) == es and int(m.group(6)) == nruns and m.group(14) == "DONE"
                and int(m.group(13), 16) == 0)
        ok += good
        print("%3d  %08x %08x %5d %08x   %s   %08x   %s   %d     %6s %4s %4s %s %s %s  %s" % (
            j, b, e, iters_of(e), x, m.group(11), es, m.group(10), int(m.group(6)), m.group(7), m.group(8),
            m.group(9), m.group(13), m.group(2), m.group(14), "OK" if good else "MISMATCH"))
    print("oracle agreement: %d/%d" % (ok, len(vecs)))
    return ok == len(vecs)


if __name__ == "__main__":
    selftest()
    if sys.argv[1] == "mkvec":
        mkvec(sys.argv[2])
    elif sys.argv[1] == "check":
        sys.exit(0 if check(sys.argv[2], sys.argv[3], int(sys.argv[4])) else 1)
