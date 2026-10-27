#!/usr/bin/env python3
"""Generate random 0/1/X vectors, run tb_kleene under iverilog with the research
prims.v, compare O5/O6/MUX against an independent Kleene evaluator."""
import random, subprocess, itertools, sys
P = "/home/user/wt-research/cells/gls/prims.v"
def kleene(vec, fn):
    xs = [i for i, c in enumerate(vec) if c == 'x']
    vals = set()
    for bits in itertools.product('01', repeat=len(xs)):
        v = list(vec)
        for i, b in zip(xs, bits): v[i] = b
        vals.add(fn(v))
    return vals.pop() if len(vals) == 1 else 'x'
INITS = [0x00E800E800E800E8, 0x96696996, 0xFFFF0000AAAACCCC, 0x8000000000000001,
         0x6996966996696996, 0xCAFEF00DDEADBEEF]
NV = 2000
rng = random.Random(20261027)
total = bad = 0
for INIT in INITS:
    vecs = []
    for _ in range(NV):
        px = rng.choice([0.1, 0.3, 0.6])
        a = ''.join('x' if rng.random() < px else rng.choice('01') for _ in range(6))  # a[0]=A1 ... a[5]=A6
        m = ''.join('x' if rng.random() < px else rng.choice('01') for _ in range(3))  # m[0]=D0,m[1]=D1,m[2]=S0
        vecs.append((a, m))
    # verilog %b reads MSB first
    open("vec.txt", "w").write(''.join(a[::-1] + ' ' + m[::-1] + '\n' for a, m in vecs))
    subprocess.check_call(["iverilog", "-gspecify", "-P", "tb.INIT=64'h%016x" % INIT, "-o", "k.vvp", "tb_kleene.v", P])
    out = subprocess.run(["vvp", "-n", "k.vvp"], capture_output=True, text=True).stdout.split('\n')
    rows = [l.split() for l in out if l and l[0] in '01xz' and len(l.split()) == 5]
    assert len(rows) == NV, (len(rows))
    nb = 0
    for (a, m), r in zip(vecs, rows):
        assert r[0] == a[::-1] and r[1] == m[::-1]
        idx = lambda v, n: sum(int(v[i]) << i for i in range(n))
        e6 = kleene(a, lambda v: str((INIT >> idx(v, 6)) & 1))
        e5 = kleene(a[:5], lambda v: str((INIT >> idx(v, 5)) & 1))
        em = kleene(m, lambda v: v[1] if v[2] == '1' else v[0])
        for name, e, g in (("O5", e5, r[2]), ("O6", e6, r[3]), ("MUX", em, r[4])):
            total += 1
            if e != g:
                nb += 1
                if nb <= 5: print("MISMATCH INIT=%016x %s a(A1..A6)=%s m(D0,D1,S0)=%s expect %s got %s" % (INIT, name, a, m, e, g))
    bad += nb
    print("INIT=%016x: %d vectors x 3 outputs, mismatches %d" % (INIT, NV, nb))
print("TOTAL comparisons %d, mismatches %d" % (total, bad))
