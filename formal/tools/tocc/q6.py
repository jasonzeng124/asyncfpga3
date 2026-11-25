import sys, pickle, collections, os
c_ = sys.argv[1]
sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
dsrc = open("/tmp/claude-0/tocc/data.py").read()
a0 = dsrc.index("def dwin(v, z):"); a1 = dsrc.index("nUp = [0]")
exec(dsrc[a0:a1].replace('def valat(n, t): return K["valat"](n, t)', ''))
DEPTH = 4
def mid_(v, w): return dl[(v, w)][2] if (v, w) in dl else 1
rows = pickle.load(open("/tmp/claude-0/tocc/data2_c%s.pkl" % c_, "rb"))
cat = collections.Counter(); ex = {}; gaps = collections.defaultdict(list)
for r in rows:
    if r[0] >= 0: continue
    _, ms, me, v, z, st, en, val, why, wa, wb = r
    u, j = st; S = eid[(u, j)]; E = eid[en] if en else None
    ts = ev[u][j] + mid_(v, u); dz = mid_(v, z)
    for (A, a, B, b) in terms(z, ts - dz, 0, 0, 0, []):
        if A is not None and sepAny(eid[A], S)[0] == -INF:
            rel = "A after S in time" if et[eid[A]] > et[S] else ("A below S in CP order" if leqP(eid[A], S) else "A before S in time, unordered")
            key = ("start", rel); cat[key] += 1; ex.setdefault(key, (r, eid[A], S)); gaps[key].append(int(et[S] - et[eid[A]]))
        if B is not None and E is not None and sepAny(E, eid[B])[0] == -INF:
            rel = "B before E in time" if et[eid[B]] < et[E] else ("E below B in CP order" if leqP(E, eid[B]) else "B after E in time, unordered")
            key = ("end", rel); cat[key] += 1; ex.setdefault(key, (r, E, eid[B])); gaps[key].append(int(et[eid[B]] - et[E]))
print("[c=%s] terms without Sep in failing guards:" % c_)
for k, n in cat.most_common(): g_ = sorted(gaps[k]); print("  %4d %s; sim gap (ps) min %d median %d max %d" % (n, k, g_[0], g_[len(g_)//2], g_[-1]))
for k, (r, X, Y) in ex.items():
    print(" example", k, "v=%s z=%s guard st=%s(%d)" % (nm[r[3]], nm[r[4]], nm[r[5][0]], r[5][1]),
          "X=%s(%d)@%d Y=%s(%d)@%d" % (nm[el[X][0]], el[X][1], el[X][2], nm[el[Y][0]], el[Y][1], el[Y][2]))
