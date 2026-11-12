# r1c: classify failing guards of a datal pickle (GuardTime failure, or claim depends on a failing claim obligation)
# usage: anal.py c pickle.  For a GuardTime end failure: E vs claim.B order and the claim node whose chain/window
# produced claim.B (traced down the covers).  For a bad claim: the bad claims it depends on whose own deps are all good.
import sys, os, pickle, collections
cc = sys.argv[1]; pk = sys.argv[2]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/r1c/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2]) if e is not None else None
D = pickle.load(open(pk, "rb")); G = D["G"]; M = D["MEMO"]; DM = D["DEPSMAP"]
def rootB(k, seen=()):
    v = M[k]; B = v["B"]
    for u, kk in (v.get("cov") or []):
        if kk in M and M[kk]["B"] == B and kk not in seen and kk != k: return rootB(kk, seen + (k,))
    return k
def badroots(k):
    out = set(); st = [k]; seen = set()
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x)
        ds = [d for d in DM.get(x, ()) if d in M and M[d].get("bad")]
        if not ds and M.get(x, {}).get("bad"): out.add(x)
        st.extend(ds)
    return out
cls = collections.Counter(); ex = {}
nf = nb = nany = 0
for x in G:
    if len(x) != 7: cls[("cycle",)] += 1; nany += 1; continue
    v, z, ms, me, cz, st, en_ = x
    gtf = min(ms, me) < 0; bad = bool(M.get(cz["key"], {}).get("bad"))
    nf += gtf; nb += bad; nany += (gtf or bad)
    if gtf:
        E = eid[en_] if en_ else None; B = cz["B"]
        if ms < 0: k = "GuardTime start"
        elif E is None or B is None: k = "end: E or B none"
        elif leqP(B, E): k = "end: claim.B causally BEFORE E"
        elif leqP(E, B): k = "end: B after E, Sep too small"
        else: k = "end: E, B unordered"
        r = rootB(cz["key"]); key = (k, "B=" + nm[el[B][0]] if B is not None else "", "root " + nm[r[0]] + " " + M[r]["kind"] + " " + str([p for p, _ in (M[r].get("phases") or [])]))
        cls[key] += 1; ex.setdefault(key, (nm[v], nm[z], s_(E) if E is not None else None, s_(B)))
    if bad:
        rs = badroots(cz["key"])
        key = ("claim depends on failing obligation", "roots " + ",".join(sorted(set(nm[r[0]] + ":" + M[r]["kind"] for r in rs))[:4]))
        cls[key] += 1; ex.setdefault(key, (nm[v], nm[z]))
print("[%s] guards %d: GuardTime fails %d, claim bad %d, failing either %d" % (pk, len(G), nf, nb, nany))
for k, n in cls.most_common(): print("%4d %s  e.g. %s" % (n, " | ".join(k), ex.get(k)))
