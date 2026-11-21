import sys, pickle, collections, os
c_ = sys.argv[1]
sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/arbh/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
dsrc = open("/tmp/claude-0/arbh/data.py").read()
a0 = dsrc.index("def dwin(v, z):"); a1 = dsrc.index("nUp = [0]")
fs = dsrc[a0:a1].replace('def valat(n, t): return K["valat"](n, t)', '')
# terms with latch identity
fs = fs.replace("out.append(((A[0], A[1]) if A else None,", "out.append((l, (A[0], A[1]) if A else None,")
fs = fs.replace("for (A, a, B, b) in out:", "for (l_, A, a, B, b) in out:")
fs = fs.replace("return [(A, a, B, b) for (A, B), (a, b) in dd.items()]", "return out")
fs = fs.replace("out.append((None, 0, None, 0))", "out.append((None, None, 0, None, 0))")
exec(fs)
DEPTH = 4
def mid_(v, w): return dl[(v, w)][2] if (v, w) in dl else 1
rows = pickle.load(open("/tmp/claude-0/arbh/data2_c%s%s.pkl" % (c_, os.environ.get("PAIR", "")), "rb"))
res = []
for r in rows:
    if r[0] >= 0: continue
    _, ms, me, v, z, st, en, val, why, wa, wb = r
    if en is None: continue
    u, j = st; E = eid[en]; S = eid[(u, j)]
    ts = ev[u][j] + mid_(v, u); dz = mid_(v, z)
    seen = set()
    for (l, A, a, B, b) in terms(z, ts - dz, 0, 0, 0, []):
        if B is None or l is None: continue
        if et[eid[B]] < et[E] and (l, B) not in seen:
            seen.add((l, B))
            res.append((v, z, st, en, val, l, B, int(et[S]), int(et[E]), int(et[eid[B]])))
print("B-before-E terms (distinct v,z,guard,latch,B):", len(res))
cz = collections.Counter((nm[x[1]], nm[x[0]]) for x in res)
print(cz.most_common())
cl = collections.Counter((nm[x[5]], nm[x[6][0]]) for x in res)
print("latches/enable nodes:", cl.most_common(10))
for x in res[:6]:
    v, z, st, en, val, l, B, tS, tE, tB = x
    print("v=%s z=%s guard [%s(%d)@%d, %s(%d)@%d) val=%d | latch %s reopened by %s(%d)@%d; z flips: %s" % (
        nm[v], nm[z], nm[st[0]], st[1], tS, nm[en[0]], en[1], tE, val, nm[l], nm[B[0]], B[1], tB,
        [t for t in (hist[z][1] if z in hist else []) if tS - 5000 < t < tE + 5000]))
pickle.dump(res, open("/tmp/claude-0/arbh/bbe_c%s.pkl" % c_, "wb"))
