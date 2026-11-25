#!/usr/bin/env python3
"""Token level: offer pair k+1 as soon as out0 holds k results (pair k's tokens may still be in flight);
check every result against gcd. Untrusted exploration. Run from formal/: python3 tools/pipe/seqtok.py"""
import sys, random, math, re
sys.path.insert(0, "tools/pipe")
import toksim
L = "lean/Formal/Net/GcdHw.lean"
rules = toksim.parse_rules(L)
names = eval(re.search(r"def chanNames : List String := (\[.*\])", open(L).read()).group(1))
N = len(names); oc = names.index("170")
vecs = [(0,0),(7,0),(12,18),(48,18),(1,1),(17,5),(0x798F20,0x12B87CA0),(0x42F,0x1CE),(0x10E,0xC0),(0x10000,0x1000),(0x18697,0x18697),(0x1E240,0xC0A14),(0x7FFFFFFF,2),(0xF4240,0xF423F),(0x24,0x3C),(0x400,0x300)]
rng = random.Random(3); bad = 0; leftover_seen = 0
for trial in range(400):
    seq = [rng.choice(vecs) for _ in range(rng.choice([2, 3]))]
    st = [[] for _ in range(N)]
    a, b = seq[0]; st[0].append(a); st[1].append(b); st[2].append(0)
    k = 1; steps = 0
    while True:
        if k < len(seq) and len(st[oc]) >= k:          # offer next pair as soon as out0 has k results
            if sum(len(q) for i, q in enumerate(st) if i not in (oc, 3)) > 0: leftover_seen += 1
            a, b = seq[k]; st[0].append(a); st[1].append(b); st[2].append(0); k += 1
        en = [i for i, r in enumerate(rules) if toksim.fire(r, st) is not None]
        if not en: break
        i = rng.choice(en); pops, pushes = toksim.fire(rules[i], st)
        for c, m in pops.items(): del st[c][:m]
        for c, v in pushes: st[c].append(v)
        steps += 1
    exp = [math.gcd(x, y) if not (x == 0x7FFFFFFF and y == 2) else None for x, y in seq]
    got = st[oc]
    if len(got) != len(seq) or any(e is not None and g != e for g, e in zip(got, exp)):
        bad += 1
        if bad < 5: print("BAD", seq, got, exp)
print("trials 400, bad", bad, "offers made with leftover tokens inside:", leftover_seen)
