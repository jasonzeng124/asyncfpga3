#!/usr/bin/env python3
"""Shard C (UNTRUSTED): GuardTime margins of every data guard under the AO Sep (forms ii/iii + iv with the final Up:
prev-below-e0 and cause-below-e0 clauses).  Claim terms as in data.py (latches in z's data cone; latches open at
the use recursed through their D inputs, depth <= 4).  usage: data2.py c"""
import sys, pickle, collections, os
c_ = sys.argv[1]
sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
dsrc = open("/tmp/claude-0/tocc/data.py").read()
a0 = dsrc.index("def dwin(v, z):"); a1 = dsrc.index("nUp = [0]")
fns = dsrc[a0:a1].replace('def valat(n, t): return K["valat"](n, t)', '')
DEPTH = 4
exec(fns)
def mid_(v, w): return dl[(v, w)][2] if (v, w) in dl else 1
guards = DATAG
rows = []; why_c = collections.Counter(); zf = collections.Counter()
for (v, z), gl in guards.items():
    dz = mid_(v, z)
    for (st, en, val) in gl:
        u, j = st; S = eid[(u, j)]; E = eid[en] if en is not None else None
        ts = ev[u][j] + mid_(v, u)
        why = []; ms = INF; me = INF; worstA = worstB = None
        for (A, a, B, b) in terms(z, ts - dz, 0, 0, 0, why):
            if A is not None:
                s, _ = sepAny(eid[A], S)
                m = s + lo_(v, u) - dwin(v, z)[1] - a if s > -INF else -INF
                if s == -INF: why.append("no Sep A=%s(%d) -> S" % (nm[A[0]], A[1]))
                if m < ms: ms = m; worstA = A
            if B is not None:
                if E is None: me = -INF; why.append("guard open-ended but data may change"); continue
                s, _ = sepAny(E, eid[B])
                m = s + dwin(v, z)[0] + b - hi_(v, u) if s > -INF else -INF
                if s == -INF: why.append("no Sep E -> B=%s(%d)" % (nm[B[0]], B[1]))
                if m < me: me = m; worstB = B
        rows.append((min(ms, me), ms, me, v, z, st, en, val, why, worstA, worstB))
        if min(ms, me) < 0:
            zf[nm[z]] += 1
            for w in set(x.split(" ")[0] + " " + x.split(" ")[1] for x in why): why_c[w] += 1
f = [r for r in rows if r[0] < 0]
print("[c=%s] guards %d: start windows failed %d, end windows failed %d, guards failed %d" % (
    c_, len(rows), sum(1 for r in rows if r[1] < 0), sum(1 for r in rows if r[2] < 0), len(f)))
print("  failed by data node:", zf.most_common())
print("  reasons:", why_c.most_common(8))
fin = sorted(r[0] for r in rows if r[0] > -INF)
print("  finite margins: min %s, 5 smallest %s" % (fin[0] if fin else None, fin[:5]))
for r in sorted(rows, key=lambda r: r[0])[:6]:
    print("   margin %s (start %s, end %s) v=%s z=%s guard st=%s(%d) en=%s val=%d why=%s" % (
        r[0], r[1], r[2], nm[r[3]], nm[r[4]], nm[r[5][0]], r[5][1], r[6] and (nm[r[6][0]], r[6][1]), r[7], r[8][:3]))
pickle.dump(rows, open("/tmp/claude-0/tocc/data2_c%s%s.pkl" % (c_, os.environ.get("PAIR", "")), "wb"))
