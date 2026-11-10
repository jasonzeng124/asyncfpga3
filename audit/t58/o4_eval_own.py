# T58: own evaluation of THE target's decoded uori4 gates: z = ((e2 & e3) != 0) | slt(e0, e1) (signed 32-bit).
# Inputs set, every other node outside S random, S random start, iterate gates driving S to a fixed point.
# Also reports how many trials a WRONG op (unsigned lt) would fail, to show the test discriminates.
# usage: o4_eval_own.py NET.json DUMP TRIALS
import json, sys, random
net = json.load(open(sys.argv[1])); gates = net["gates"]
S, A = [], []
for l in open(sys.argv[2]):
    f = l.split()
    if f[0] == 'S': S.append(int(f[1]))
    elif f[0] == 'A': A.append(tuple(map(int, f[1:])))
    elif f[0] == 'C': e2, e3, z = map(int, f[1:])
Sset = set(S); drv = {g["out"]: g for g in gates if g["out"] in Sset}
print("S", len(S), "driven", len(drv))
e0 = [x[1] for x in sorted(A)]; e1 = [x[2] for x in sorted(A)]
print("inputs inside S:", len(Sset & set(e0 + e1 + [e2, e3])), "z in S:", z in Sset)
sg = lambda a: a - (1 << 32) if a >> 31 else a
rng = random.Random(2058); bad = nonconv = wrongdetect = 0
T = int(sys.argv[3])
edge = [0, 1, 0x7fffffff, 0x80000000, 0xffffffff]
for t in range(T):
    if t < 25: a, b = edge[t // 5], edge[t % 5]
    elif t % 3 == 0: a = rng.getrandbits(32); b = a ^ (1 << rng.randrange(32))
    else: a, b = rng.getrandbits(32), rng.getrandbits(32)
    c, d = rng.getrandbits(1), rng.getrandbits(1)
    v = {}
    get = lambda n: v.get(n) if n in v else v.setdefault(n, rng.random() < 0.5)
    for i in range(32): v[e0[i]] = bool((a >> i) & 1); v[e1[i]] = bool((b >> i) & 1)
    v[e2] = bool(c); v[e3] = bool(d)
    for n in S: v[n] = rng.random() < 0.5
    for it in range(400):
        ch = 0
        for n in S:
            g = drv[n]; ad = sum((1 << p) for p, i in enumerate(g["ins"]) if get(i))
            nv = bool((g["init"] >> ad) & 1)
            if nv != v[n]: v[n] = nv; ch += 1
        if ch == 0: break
    else: nonconv += 1; continue
    want = int((c & d) != 0 or sg(a) < sg(b)); wrong = int((c & d) != 0 or a < b)
    if int(v[z]) != want: bad += 1; print("MISMATCH", hex(a), hex(b), c, d, int(v[z]), want)
    if int(v[z]) != wrong: wrongdetect += 1
print("trials", T, "non-converged", nonconv, "mismatches", bad, "| unsigned-lt control would mismatch", wrongdetect)
