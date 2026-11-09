# T54: own evaluation (uaddi0: z = e0 + e1 mod 2^32) of THE target's decoded gates for C's uselect1 claim: set the 64 input nodes (e0, e1 words, bit i =
# node of index i) and random values on every other node outside S, then settle every gate driving S (iterate to a fixed
# point), and compare the 32 z nodes with |e0 - e1| in 32-bit two's complement as the claim's op
# (d = e0 - e1; d > -1 signed ? d : 0 - d).  usage: u1_eval_own.py NET.json U1_DUMP TRIALS
import json, sys, random
net = json.load(open(sys.argv[1])); gates = net["gates"]
S, IO = [], []
for l in open(sys.argv[2]):
    f = l.split()
    if f[0] == 'S': S.append(int(f[1]))
    elif f[0] == 'IO': IO.append(tuple(map(int, f[1:])))
Sset = set(S); drv = {}
for g in gates:
    if g["out"] in Sset: drv[g["out"]] = g
missing = [n for n in S if n not in drv]
print("S", len(S), "with a driving gate", len(drv), "without:", len(missing))
e0 = [x[1] for x in sorted(IO)]; e1 = [x[2] for x in sorted(IO)]; z = [x[3] for x in sorted(IO)]
print("inputs inside S:", len(Sset & set(e0 + e1)))
rng = random.Random(2026); bad = 0; nonconv = 0
def op(a, b):
    d = (a - b) & 0xffffffff
    ds = d - (1 << 32) if d >> 31 else d
    return (a + b) & 0xffffffff
T = int(sys.argv[3])
for t in range(T):
    a = rng.getrandbits(32) if t > 3 else [0, 1, 0xffffffff, 0x80000000][t]; b = rng.getrandbits(32) if t > 3 else [0, 0x80000000, 1, 0][t]
    v = {}
    get = lambda n: v.get(n) if n in v else v.setdefault(n, rng.random() < 0.5)
    for i in range(32): v[e0[i]] = bool((a >> i) & 1); v[e1[i]] = bool((b >> i) & 1)
    for n in S: v[n] = rng.random() < 0.5            # arbitrary start for S
    for it in range(400):
        ch = 0
        for n in S:
            g = drv[n]; ad = sum((1 << p) for p, i in enumerate(g["ins"]) if get(i))
            nv = bool((g["init"] >> ad) & 1)
            if nv != v[n]: v[n] = nv; ch += 1
        if ch == 0: break
    else: nonconv += 1; continue
    got = sum((1 << i) for i in range(32) if v[z[i]])
    if got != op(a, b): bad += 1; print("MISMATCH", hex(a), hex(b), hex(got), hex(op(a, b)))
print("trials", T, "non-converged", nonconv, "mismatches", bad)
