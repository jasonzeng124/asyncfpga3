# r1c counterfactual: would B's UnionUp Up-join (Formal/Cells/UnionUp.lean, UnionUpOK: Up(c1.B -> c2.A) = u,
# c2.a + u <= c1.b, 1 <= c2.a) join the latch-chain links that ChainOK's Sep join truncated?  usage: upjoin.py c pickle
import sys, os, pickle, collections, threading
cc = sys.argv[1]; pk = sys.argv[2]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/r1c/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
os.environ.setdefault("RELD", "99"); os.environ.setdefault("RELK", "16"); os.environ.setdefault("RELTRY", "64")
exec(open("/tmp/claude-0/r1c/relup.py").read())
sys.setrecursionlimit(200000); threading.stack_size(1024 * 1024 * 1024)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2]) if e is not None else None
T = pickle.load(open(pk, "rb"))["TRUNC"]
def main():
    res = collections.Counter(); ex = {}
    seen = set()
    for (Q, p1, p2, A2, B1, b1, a2, d) in T:
        if (Q, A2, B1) in seen: continue
        seen.add((Q, A2, B1))
        if A2 is None or B1 is None: res[(p1 + "->" + p2, "none")] += 1; continue
        order = "B1<=A2" if leqP(B1, A2) else ("A2<=B1" if leqP(A2, B1) else "unordered")
        u = up_get(B1, A2, RELD) if tm[A2] >= tm[B1] else None
        ok = u is not None and a2 >= 1 and a2 + u <= b1
        k = (p1 + "->" + p2, order, "Up-join OK" if ok else ("no Up" if u is None else "Up too large"))
        res[k] += 1
        if k not in ex: ex[k] = (nm[Q], s_(B1), b1, s_(A2), a2, u)
    for k, n in sorted(res.items()): print("%5d %s  e.g. %s" % (n, " | ".join(k), ex.get(k)), flush=True)
th = threading.Thread(target=main); th.start(); th.join()
