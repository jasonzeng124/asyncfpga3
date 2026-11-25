#!/usr/bin/env python3
"""diffcheck.py ORIG.mlir REWRITTEN.mlir [--vectors N] [--seed S] [--limit STEPS] [--sched K]

Differential check of a rewrite with hsinterp.py: run both files on the same inputs (data arguments: edge values
0, 1, 2, -1, INT_MIN, INT_MAX of their width, small values, random; memories: all 0, all -1, small random, full-range
random) under the in-order schedule and K seeded random schedules each, and compare the `end` tokens (first value
and count) and every memory's final contents.  Prints one line per vector and a summary line:

  DIFF-PASS kernel n/n          every vector agreed on every schedule (and quiesced)
  DIFF-FAIL kernel ...          some vector disagreed: the vector is printed
  INCONCLUSIVE kernel ...       the ORIGINAL itself is schedule dependent or hit the step limit on some vector
"""
import argparse
import os
import random
import re
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hsinterp  # noqa: E402


def edge(w):
    vals = [0, 1, 2, (1 << w) - 1]
    if w > 2:
        vals += [1 << (w - 1), (1 << (w - 1)) - 1, 3, 7, 10, 100, 255, 256]
    return [v & ((1 << w) - 1) for v in vals]


def make_vectors(sim, n, rng):
    data = [(a, int(re.search(r'<i(\d+)>', t).group(1))) for a, t in sim.args if t.startswith('!handshake.channel')]
    mems = [(a, len(sim.mems[a]), sim.memw[a]) for a, t in sim.args if t.startswith('memref')]
    vecs = []
    for i in range(n):
        v = {}
        for a, w in data:
            e = edge(w)
            if i < len(e):
                v[a] = e[(i + data.index((a, w))) % len(e)]
            elif i % 3 == 0:
                v[a] = rng.randrange(-300, 301) & ((1 << w) - 1)
            else:
                v[a] = rng.randrange(1 << w)
        m = {}
        for a, size, w in mems:
            kind = i % 5
            if kind == 0:
                m[a] = [0] * size
            elif kind == 1:
                m[a] = [(1 << w) - 1] * size
            elif kind == 2:
                m[a] = [rng.randrange(-8, 9) & ((1 << w) - 1) for _ in range(size)]
            elif kind == 3:
                m[a] = [rng.randrange(0, size) for _ in range(size)]   # in-range indices (gather-like kernels)
            else:
                m[a] = [rng.randrange(1 << w) for _ in range(size)]
        vecs.append((v, m))
    return vecs


def one(text, v, m, limit, seed):
    s = hsinterp.Sim(text)
    r = s.run(v, m, limit=limit, seed=seed)
    return r


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('orig')
    ap.add_argument('rw')
    ap.add_argument('--vectors', type=int, default=16)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--limit', type=int, default=3_000_000)
    ap.add_argument('--sched', type=int, default=1)
    ap.add_argument('--budget', type=float, default=600.0, help='wall seconds; stop adding vectors after this')
    a = ap.parse_args()
    to, tr = open(a.orig).read(), open(a.rw).read()
    name = os.path.basename(a.orig).replace('.mlir', '')
    try:
        s0 = hsinterp.Sim(to)
        hsinterp.Sim(tr)
    except hsinterp.Unsupported as e:
        print(f'UNSUPPORTED {name}: {e}')
        return 3
    rng = random.Random(a.seed)
    vecs = make_vectors(s0, a.vectors, rng)
    t0 = time.time()
    npass = nfail = ninc = 0
    for i, (v, m) in enumerate(vecs):
        if time.time() - t0 > a.budget:
            print(f'  budget reached after {i} vectors')
            break
        scheds = [None] + [a.seed * 1000 + i * 10 + k for k in range(a.sched)]
        ro = [one(to, v, m, a.limit, s) for s in scheds]
        rr = [one(tr, v, m, a.limit, s) for s in scheds]
        key = lambda r: (r['status'], r['ends'], r['mems'])
        vs = {k[1:]: x for k, x in v.items()}
        if any(r['status'] != 'quiesced' for r in ro) or any(key(r) != key(ro[0]) for r in ro):
            ninc += 1
            print(f'  vec {i} {vs}: INCONCLUSIVE original: ' + ', '.join(f"{r['status']} ends={r['ends']}" for r in ro))
            if any(key(x) != key(ro[0]) for x in rr) and all(r['status'] == 'quiesced' for r in rr + ro):
                print('     (rewritten differs too)')
            continue
        bad = [k for k, x in enumerate(rr) if key(x) != key(ro[0])]
        if bad:
            nfail += 1
            k = bad[0]
            dm = [n for n in ro[0]['mems'] if ro[0]['mems'][n] != rr[k]['mems'][n]]
            print(f'  vec {i} {vs} mems=[{",".join(f"{n}:{m[n][:4]}..." for n in m)}]: FAIL sched {scheds[k]}: '
                  f"orig {ro[0]['status']} ends={ro[0]['ends']} | rw {rr[k]['status']} ends={rr[k]['ends']} "
                  f"memdiff={dm}")
        else:
            npass += 1
            print(f"  vec {i} {vs}: ok ends={ro[0]['ends']} steps={ro[0]['steps']}/{rr[0]['steps']} oob={ro[0]['oob']}")
    tot = npass + nfail + ninc
    if nfail:
        print(f'DIFF-FAIL {name} {nfail} failing of {tot} ({ninc} inconclusive)')
        return 1
    if ninc:
        print(f'INCONCLUSIVE {name} {npass}/{tot} agreed, {ninc} inconclusive (original schedule-dependent or limit)')
        return 2
    print(f'DIFF-PASS {name} {npass}/{tot} vectors x {1 + a.sched} schedules')
    return 0


if __name__ == '__main__':
    sys.exit(main())
