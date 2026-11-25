#!/usr/bin/env python3
"""bsub1: failing claim obligations by kind, guards blocked per kind (dependency closure), loop-cover analysis.
usage: obl.py PKL c [label]"""
import sys, pickle, collections
sys.path.insert(0, '/tmp/claude-0/bsub1/tocc')
from classify import load
C = load(); nm = C['names']; EX = C['EXACT']
PK = sys.argv[1]; c = int(sys.argv[2]); lab = sys.argv[3] if len(sys.argv) > 3 else PK
H = pickle.load(open('/tmp/claude-0/bsub1/tocc/hist_c%d.pkl' % c, 'rb')); t0 = H['R'] - 1; hist = H['hist']
el = []
for n in sorted(EX):
    for k, t in enumerate([x for x in (hist[n][1] if n in hist else []) if x > t0]): el.append((n, k, t))
def E(e): return None if e is None else "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
P = pickle.load(open(PK, 'rb')); F = P['FAILS']; DM = P['DEPSMAP']; M = P['MEMO']
print("[%s c=%d] passes %s" % (lab, c, P.get('PASSLOG')))
def kclass(kind, side):
    if kind.startswith("loop cover"): return "%s %s" % (kind, side)
    if kind.startswith("ChainOK comb"): return "comb-segment link"
    return kind
cnt = collections.Counter(); claims = collections.defaultdict(set)
for ck, L in F.items():
    for (kind, side, m, det) in L:
        cnt[kclass(kind, side)] += 1; claims[kclass(kind, side)].add(ck)
print("  failing items by kind (items / distinct claims):")
for k, n in cnt.most_common(): print("    %-45s %5d / %5d" % (k, n, len(claims[k])))
# guard closure
memo_cl = {}
def closure(k):
    seen = set(); st = [k]
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x); st.extend(DM.get(x, ()))
    return seen
gb = collections.Counter(); gonly = collections.Counter(); nblk = 0; ng = 0
for x in P['G']:
    if len(x) != 7: continue
    ng += 1; cz = x[4]; cl = closure(cz.get('key'))
    ks = set()
    for k in cl:
        for (kind, side, m, det) in F.get(k, ()): ks.add(kclass(kind, side))
    if ks: nblk += 1
    for k in ks: gb[k] += 1
    if len(ks) == 1: gonly[next(iter(ks))] += 1
print("  guards %d, blocked by any failing obligation %d" % (ng, nblk))
for k, n in gb.most_common(): print("    %-45s blocks %3d guards (sole kind for %d)" % (k, n, gonly[k]))
# loop covers
LC = P['LOOPC']
fl = [r for r in LC if r[6] < 0]
print("  loop-cover checks: %d (%d failing); by (src, side, why): %s" % (len(LC), len(fl), collections.Counter((r[0], r[5], r[7]) for r in fl).most_common()))
pairs = collections.Counter((nm[r[2]], nm[r[4][0]], r[5], r[7]) for r in fl)
print("  failing loop covers by (consumer gate, cover node, side, why), top 12:")
for k, n in pairs.most_common(12): print("    %4d %s" % (n, k))
fin = sorted([r for r in fl if r[6] > -1e18], key=lambda r: r[6])
if fin:
    print("  finite shortfalls: n=%d, worst %d, median %d" % (len(fin), fin[0][6], fin[len(fin) // 2][6]))
for cls, sel in (("no Sep", lambda r: r[7] == "no Sep"), ("short", lambda r: r[7] == "short"), ("consumer none", lambda r: "none" in r[7])):
    ex = [r for r in fl if sel(r)][:1]
    for r in ex:
        (A, a, B, b), (wA, wa, wB, wb) = r[8], r[9]
        print("  EXAMPLE %s [%s %s]: consumer %s cover %s(pin %s) margin %s; consumer A,a=%s,%s B,b=%s,%s; cover A,a=%s,%s B,b=%s,%s" % (
            cls, r[0], r[5], nm[r[2]], nm[r[4][0]], nm[r[3]], r[6] if r[6] > -1e18 else '-inf', E(A), a, E(B), b, E(wA), wa, E(wB), wb))
