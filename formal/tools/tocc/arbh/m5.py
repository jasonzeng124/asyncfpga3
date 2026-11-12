import sys, os
c_ = sys.argv[1]; BN = sys.argv[2]
sys.argv = ["datal.py", c_]
src = open("/tmp/claude-0/arbh/datal.py").read(); src = src[:src.index("# ---------------- guards")]
exec(src)
def mid_(v, w): return dl[(v, w)][2] if (v, w) in dl else 1
idn = {n_: i for i, n_ in enumerate(nm)}
bn = idn[BN]
LOG = []
orig = claim
def claim(n, t, t2=None):
    r = orig(n, t, t2)
    if isinstance(r, dict) and r.get("B") is not None and el[r["B"]][0] == bn: LOG.append((nm[n], t, t2, r.get("kind"), el[r["B"]][1], r.get("b")))
    return r
globals()["claim"] = claim
done = 0
for (v, z), gl in DATAG.items():
    for (st, en_, val) in gl:
        if en_ is None: continue
        u, j = st; S = eid[(u, j)]; E = eid[en_]
        ts = ev[u][j] + mid_(v, u); te_ = ev[en_[0]][en_[1]] + mid_(v, en_[0])
        LOG.clear(); memo.clear()
        CTX.append(tuple(sorted([S, E])))
        cz = claim(z, ts - mid_(v, z), te_ - mid_(v, z))
        CTX.pop()
        if isinstance(cz, dict) and cz["B"] is not None and el[cz["B"]][0] == bn and sep(E, cz["B"]) == NEG:
            print("guard v=%s z=%s [%s(%d)@%d, %s(%d)@%d) claim.B=%s(%d)@%d b=%d" % (nm[v], nm[z], nm[u], j, ev[u][j], nm[en_[0]], en_[1], ev[en_[0]][en_[1]], BN, el[cz["B"]][1], el[cz["B"]][2], cz["b"]))
            for x in LOG[:25]: print("   ", x)
            print("  events of", BN, ev[bn], "| E-B ordering: sep(E,B)", sep(E, cz["B"]), "sep(B,E)", sep(cz["B"], E))
            done += 1
            if done >= 1: raise SystemExit
