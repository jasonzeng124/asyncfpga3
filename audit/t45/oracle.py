#!/usr/bin/env python3
"""Auditor's own collatz64 oracle (T45). No research code imported.

Kernel semantics from /root/wt-r34/cloud/fixtures/frontend/collatz64/comp/cf.mlir:
  collatz64(n:i64) -> i32: if n == 1 return 0; steps = 0; loop { n = (n & 1) == 0 ? n >>s 1 : 3n+1 (mod 2^64);
  steps += 1 (mod 2^32); if n == 1 break }; return steps.
Bench (hw/gen_bench.py, read only): n = {op1, op0}; FIXED mode masks the high word with 0 and maps n==0 to 1,
so the kernel sees n = op0 (or 1 when op0 == 0). SIG per batch = fold over runs of sig = rotl1(sig) ^ result,
from 0; ODATA = the result.

usage: oracle.py mkvec OUT.hex           -- the 14-vector set described in results.tsv's header
       oracle.py check VEC.hex LOG NRUNS -- compare every BENCHRES line of LOG with the oracle
"""
import re, sys

M = 0xFFFFFFFF
M64 = (1 << 64) - 1


def collatz64(op0, op1):
    n = op0 & M                     # FIXED-mode domain mask: high word & 0
    if n == 0:
        n = 1
    if n == 1:
        return 0
    steps = 0
    while True:
        if n & 1 == 0:
            n = n >> 1              # n stays positive here, so >>s == >>
        else:
            n = (3 * n + 1) & M64
            assert n < (1 << 63), "trajectory leaves int64"
        steps = (steps + 1) & M
        if n == 1:
            return steps


def sig(x, nruns):
    s = 0
    for _ in range(nruns):
        s = (((s << 1) & M) | (s >> 31)) ^ x
    return s


def mkvec(out):
    # results.tsv header: "14 vectors: n=2^k for loop_cost.sh's k and n=27/97/871/77031 on the 3n+1 path";
    # loop_cost.sh collatz64 POINTS="1 2 4 8 12 16 20 24 28 30". Order is the auditor's choice.
    v = [(1 << k, 0) for k in (1, 2, 4, 8, 12, 16, 20, 24, 28, 30)] + [(n, 0) for n in (27, 97, 871, 77031)]
    with open(out, "w") as f:
        for a, b in v:
            f.write("%08x %08x\n" % (a, b))
    print("wrote %d vectors to %s" % (len(v), out))


def check(vec, log, nruns):
    words = open(vec).read().split()
    vecs = [(int(words[i], 16), int(words[i + 1], 16)) for i in range(0, len(words), 2)]
    rows = {}
    for ln in open(log):
        m = re.search(r"BENCHRES batch=(\d+) .*?op0=([0-9a-f]+) op1=([0-9a-f]+) n=(\d+) completed=(\d+) "
                      r"cycles=(\d+) .*?latmin=(\d+) latmax=(\d+) sig=([0-9a-f]+) odata=([0-9a-f]+) mism_st=(\S+) "
                      r"ill=([0-9a-f]+) .* (DONE|HANG)\s*$", ln)
        if m:
            rows[int(m.group(1))] = m
    ok = 0
    print("vec  n(op0)    op1       exp_steps sim_odata  exp_sig    sim_sig    compl cycles lmin lmax  ill      state  verdict")
    for j, (a, b) in enumerate(vecs):
        e = collatz64(a, b); es = sig(e, nruns)
        m = rows.get(j)
        if not m:
            print("%3d  %08x  %08x  %9d  MISSING" % (j, a, b, e)); continue
        good = (int(m.group(2), 16) == a and int(m.group(3), 16) == b and int(m.group(10), 16) == e
                and int(m.group(9), 16) == es and int(m.group(5)) == nruns and m.group(13) == "DONE"
                and int(m.group(12), 16) == 0)
        ok += good
        print("%3d  %08x  %08x  %9d  %08x   %08x   %s   %d     %6s %4s %4s  %s %s  %s" % (
            j, a, b, e, int(m.group(10), 16), es, m.group(9), int(m.group(5)), m.group(6), m.group(7), m.group(8),
            m.group(12), m.group(13), "OK" if good else "MISMATCH"))
    print("oracle agreement: %d/%d" % (ok, len(vecs)))
    return ok == len(vecs)


if __name__ == "__main__":
    if sys.argv[1] == "mkvec":
        mkvec(sys.argv[2])
    elif sys.argv[1] == "selftest":
        for n in (27, 97, 871, 77031, 1 << 30, 1, 0, 2):
            print(n, collatz64(n, 0))
    else:
        sys.exit(0 if check(sys.argv[2], sys.argv[3], int(sys.argv[4])) else 1)
