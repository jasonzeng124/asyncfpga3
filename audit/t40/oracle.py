#!/usr/bin/env python3
"""Auditor's own xorshift oracle (T40). No research code imported.

Kernel semantics from cloud/fixtures/frontend/xorshift/comp/cf.mlir (and kernels/xorshift/xorshift.c):
  xorshift(seed:i32 arg0, rounds:i32 arg1): x = seed; for i in 0..rounds-1 (signed compare 0 < rounds):
      x ^= x << 13; x ^= x >> 17 (logical); x ^= x << 5     (all mod 2^32)
Bench (hw/gen_bench.py): op0 -> arg0 (seed), op1 -> arg1 (rounds), FIXED mode masks rounds with 0xFFF;
SIG per batch = fold over runs of sig = rotl1(sig) ^ result, starting at 0; ODATA = the result.

usage: oracle.py mkvec OUT.hex           -- write the 17-vector file (op0 op1 per line)
       oracle.py check VEC.hex LOG NRUNS -- compare every BENCHRES line of LOG with the oracle
"""
import random, re, sys

M = 0xFFFFFFFF


def xs(seed, rounds):
    x = seed & M
    r = rounds & 0xFFF                      # bench domain mask (FIXED mode)
    for _ in range(r):
        x ^= (x << 13) & M
        x ^= x >> 17
        x ^= (x << 5) & M
    return x


def sig(x, nruns):
    s = 0
    for _ in range(nruns):
        s = (((s << 1) & M) | (s >> 31)) ^ x
    return s


def mkvec(out):
    # simcheck's six hand-picked vectors (bdc/simcheck.py VECTORS["xorshift"], read, not imported),
    # fusion_bench's 8 seeded randoms (random.Random(20261026), seed in [1,2^31), rounds in [0,9)),
    # and rounds 64/200/1000 at the C main()'s seed, as research's results.tsv header describes.
    v = [(2463534242, 0), (2463534242, 1), (2463534242, 2), (2463534242, 4), (1, 3), (-1, 2)]
    rng = random.Random(20261026)
    for _ in range(8):
        s = rng.randrange(1, 1 << 31); r = rng.randrange(0, 9)
        v.append((s, r))
    v += [(2463534242, 64), (2463534242, 200), (2463534242, 1000)]
    with open(out, "w") as f:
        for s, r in v:
            f.write("%08x %08x\n" % (s & M, r & M))
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
    ok = 0; lat = {}
    print("vec  seed      rounds  exp_odata  sim_odata  exp_sig    sim_sig    compl lmin lmax  ill      state  verdict")
    for j, (s, r) in enumerate(vecs):
        e = xs(s, r); es = sig(e, nruns)
        m = rows.get(j)
        if not m:
            print("%3d  %08x %6d  %08x   MISSING" % (j, s, r, e)); continue
        good = (int(m.group(2), 16) == s and int(m.group(3), 16) == r and int(m.group(10), 16) == e
                and int(m.group(9), 16) == es and int(m.group(5)) == nruns and m.group(13) == "DONE"
                and int(m.group(12), 16) == 0)
        ok += good
        lat[r] = (int(m.group(7)), int(m.group(8)), int(m.group(6)))
        print("%3d  %08x %6d  %08x   %s   %08x   %s   %d     %4s %4s  %s %s  %s" % (
            j, s, r, e, m.group(10), es, m.group(9), int(m.group(5)), m.group(7), m.group(8), m.group(12),
            m.group(13), "OK" if good else "MISMATCH"))
    print("oracle agreement: %d/%d" % (ok, len(vecs)))
    if 200 in lat and 1000 in lat:
        for k, name in ((0, "latmin"), (1, "latmax")):
            print("per_round (%s): (%d - %d)/800 = %.4f" % (name, lat[1000][k], lat[200][k],
                                                         (lat[1000][k] - lat[200][k]) / 800))
        print("per_round (cycles/run): (%d - %d)/(800*%d) = %.4f" % (
            lat[1000][2], lat[200][2], nruns, (lat[1000][2] - lat[200][2]) / 800 / nruns))
    return ok == len(vecs)


if __name__ == "__main__":
    if sys.argv[1] == "mkvec":
        mkvec(sys.argv[2])
    else:
        sys.exit(0 if check(sys.argv[2], sys.argv[3], int(sys.argv[4])) else 1)
