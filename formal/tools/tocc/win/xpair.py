#!/usr/bin/env python3
"""cross-pair window identity (UNTRUSTED): usage xpair.py c P Q level jP jQ [jP jQ ...]; level main|inner"""
import sys, pickle, collections
import numpy as np
sys.argv_saved = sys.argv[:]
c = int(sys.argv[1]); P, Q, lev = sys.argv[2], sys.argv[3], sys.argv[4]; js = list(map(int, sys.argv[5:]))
sys.argv = [sys.argv[0], str(c), P, Q]
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    exec(open("/tmp/claude-0/win/win.py").read().split("RES = {}")[0])
P, Q = sys.argv_saved[2], sys.argv_saved[3]
def prep(D, h):
    w = windows(D, h); el = D["el"]; cnt = collections.defaultdict(collections.Counter)
    for e, (n, k, t) in enumerate(el): cnt[int(w[e])][n] += 1
    off = {}; run = collections.Counter()
    for j in range(-1, int(w.max()) + 2): off[j] = dict(run); run.update(cnt[j])
    if "DS" not in D:
        D["DS"] = Dsets(D); rd = collections.defaultdict(set)
        for v, S in D["DS"].items():
            for a in S: rd[a].add(v)
        D["RD"] = rd
    return w, cnt, off
def sigx(D, off, h, x, j):
    el = D["el"]; xi = D["xi"]; n, k, t = el[x]
    rel = lambda p: (nm[el[p][0]], el[p][1] - off[j].get(el[p][0], 0))
    A = frozenset(frozenset(rel(p) for p in alt) for alt in D["alts"][x])
    Ls = {}
    for v in D["RD"][n]:
        for b in D["DS"][v]:
            if b != n: Ls[(nm[v], nm[b])] = min(int(D["VC"][x, xi[b]]), D["OVER"].get(v, {}).get((n, k, b), 99)) - off[j].get(b, 0)
    RT = frozenset(rel(p) for p in D["rt"].get(x, []))
    th = el[D["eid"][(h, 2 * j)]][2]
    return A, Ls, RT, t - th
res = []
for jP, jQ in zip(js[::2], js[1::2]):
    out = []
    for X in (R[P], R[Q]):
        h = pick_head(X, P if X is R[P] else Q, (lambda Y: 2 * Y["tc"]["L9"]) if lev == "main" else (lambda Y: 2 * Y["tc"]["L10"]))
        out.append((X, h) + prep(X, h))
    (DP, hP, wP, cP, oP), (DQ, hQ, wQ, cQ, oQ) = out
    dc = [n for n in set(cP[jP]) | set(cQ[jQ]) if cP[jP][n] != cQ[jQ][n]]
    dA = dL = dR = 0; dT = []
    for n in cP[jP]:
        if n in dc: continue
        for i in range(cP[jP][n]):
            s0 = sigx(DP, oP, hP, DP["eid"][(n, oP[jP].get(n, 0) + i)], jP); s1 = sigx(DQ, oQ, hQ, DQ["eid"][(n, oQ[jQ].get(n, 0) + i)], jQ)
            dA += s0[0] != s1[0]; dL += s0[1] != s1[1]; dR += s0[2] != s1[2]; dT.append(s1[3] - s0[3])
    oddn = [nm[n] for n in R[P]["xs"] if (oP[jP].get(n, 0) - oQ[jQ].get(n, 0)) % 2]; odd = "%d %s" % (len(oddn), oddn[:3])
    s = "c=%d %s %s w%d vs %s w%d: count-diff nodes %d %s; events %d: alt-diff %d, L-diff %d, RT-diff %d, dt %s; nodes with odd offset diff %s" % (
        c, lev, P, jP, Q, jQ, len(dc), [nm[n] for n in dc[:4]], sum(cP[jP].values()), dA, dL, dR, (min(dT), max(dT)) if dT else None, odd)
    print(s); res.append(s)
open("/tmp/claude-0/win/xpair_c%d.txt" % c, "a").write("\n".join(res) + "\n")
