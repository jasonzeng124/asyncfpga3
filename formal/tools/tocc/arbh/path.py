# print the claim-end (B) binding path from a failing guard's claim down to its root claim
import sys, os, pickle
cc = sys.argv[1]; pk = sys.argv[2]; N = int(sys.argv[3]) if len(sys.argv) > 3 else 1
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/arbh/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2]) if e is not None else None
D = pickle.load(open(pk, "rb")); M = D["MEMO"]
n = 0
for x in D["G"]:
    if len(x) != 7 or min(x[2], x[3]) >= 0: continue
    v, z, ms, me, cz, st, en_ = x
    print("guard", nm[v], nm[z], "E", s_(eid[en_]) if en_ else None)
    k = cz["key"]; seen = set()
    while k not in seen:
        seen.add(k); w = M[k]
        print("   ", nm[k[0]], k[1:3], w["kind"], "A", s_(w["A"]), w["a"], "B", s_(w["B"]), w["b"], w.get("phases"))
        nxt = [kk for u, kk in (w.get("cov") or []) if kk in M and M[kk]["B"] == w["B"]]
        if not nxt: break
        k = nxt[0]
    n += 1
    if n >= N: break
