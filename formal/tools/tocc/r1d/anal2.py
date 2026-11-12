# r1d: deepest truncated claim on each failing guard's claim-end (B) binding path, with its failing ChainOK step
import sys, os, pickle, collections
cc = sys.argv[1]; pk = sys.argv[2]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/r1d/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2]) if e is not None else None
D = pickle.load(open(pk, "rb")); M = D["MEMO"]
TR = collections.defaultdict(list)
for t in D["TRUNC"]: TR[t[0]].append(t)
cls = collections.Counter(); ex = {}
for x in D["G"]:
    if len(x) != 7 or min(x[2], x[3]) >= 0: continue
    v, z, ms, me, cz, st, en_ = x
    k = cz["key"]; seen = set(); deep = None; last = k
    while k not in seen:
        seen.add(k); w = M[k]; last = k
        if w.get("trunc") is not None: deep = k
        nxt = [kk for u, kk in (w.get("cov") or []) if kk in M and M[kk]["B"] == w["B"]]
        if not nxt: break
        k = nxt[0]
    if deep is None:
        key = ("no truncated claim on the path", "root " + nm[last[0]] + " " + M[last]["kind"], "B=" + (nm[el[M[last]["B"]][0]] if M[last]["B"] is not None else "None"))
    else:
        w = M[deep]; tr = [t for t in TR[deep[0]] if t[4] == w["trunc"]]
        t = tr[0] if tr else None
        key = ("deepest truncated: " + nm[deep[0]], ("%s->%s c2.A=%s c1.B=%s" % (t[1], t[2], s_(t[3]), s_(t[4]))) if t else "?")
    cls[key] += 1; ex.setdefault(key, (nm[v], nm[z], s_(eid[en_]) if en_ else None, s_(cz["B"])))
print("[%s] failing guards %d" % (pk, sum(cls.values())))
for k, n in cls.most_common(): print("%4d %s  e.g. %s" % (n, " | ".join(k), ex[k]))
