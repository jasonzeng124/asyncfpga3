# r1c counterfactual: B's JoinAnc (Formal/Cells/UnionUp.lean): common ancestor e0, Sep(e0 -> c1.B) = s, Up(e0 -> c2.A) = u,
# c2.a + u <= c1.b + s.  For the truncated links of a datal pickle whose node is in NODES (or all links when NODES = all).
import sys, os, pickle, collections, threading
cc = sys.argv[1]; pk = sys.argv[2]; NODES = sys.argv[3].split(",")
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/race/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
os.environ.setdefault("RELD", "99"); os.environ.setdefault("RELK", "16"); os.environ.setdefault("RELTRY", "64")
exec(open("/tmp/claude-0/race/relup.py").read())
sys.setrecursionlimit(200000); threading.stack_size(1024 * 1024 * 1024)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2]) if e is not None else None
T = pickle.load(open(pk, "rb"))["TRUNC"]
def main():
    seen = set()
    for (Q, p1, p2, A2, B1, b1, a2, d) in T:
        if NODES != ["all"] and nm[Q] not in NODES: continue
        if A2 is None or B1 is None or (A2, B1) in seen: continue
        seen.add((A2, B1))
        m = np.minimum(VCP[A2], VCP[B1]); best = None
        for x in np.nonzero(m)[0]:
            e0 = eid[(xs[x], int(m[x]) - 1)]
            CURD[0] = RELD; s, _ = sepAny(e0, B1); CURD[0] = 0
            if s == -INF: continue
            u = up_get(e0, A2, RELD)
            if u is None: continue
            if best is None or s - u > best[0]: best = (s - u, e0, s, u)
        need = a2 - b1
        print("%s %s->%s: c1.B %s b %d, c2.A %s a %d; need Sep-Up >= %d; best %s" % (nm[Q], p1, p2, s_(B1), b1, s_(A2), a2, need,
              None if best is None else "%d via %s (Sep %d, Up %d) -> %s" % (best[0], s_(best[1]), best[2], best[3], "JOINS" if best[0] >= need else "short by %d" % (need - best[0]))), flush=True)
th = threading.Thread(target=main); th.start(); th.join()
