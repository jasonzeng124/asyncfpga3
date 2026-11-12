# the latch-chain truncations that end claims at an early end event; can the relative Up repair the union?
import sys, os, pickle, collections, threading
cc = sys.argv[1]; pk = sys.argv[2]; BN = sys.argv[3].split(",")
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/r1b/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
os.environ.setdefault("RELD", "99"); os.environ.setdefault("RELK", "16"); os.environ.setdefault("RELTRY", "64")
exec(open("/tmp/claude-0/r1b/relup.py").read())
sys.setrecursionlimit(200000); threading.stack_size(1024 * 1024 * 1024)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2]) if e is not None else None
T = pickle.load(open(pk, "rb"))["TRUNC"]
sel = collections.Counter(); pairs = {}
for (Q, p1, p2, A2, B1, b1, a2, d) in T:
    if B1 is None or nm[el[B1][0]] not in BN: continue
    sel[(nm[Q], p1, p2, s_(B1))] += 1
    pairs.setdefault((A2, B1), []).append((nm[Q], p1, p2, b1, a2, d))
def main():
    for k, n in sel.most_common(): print("%3d %s" % (n, k))
    PH = os.environ.get("PH"); items_ = [(k_, L_) for k_, L_ in pairs.items() if PH is None or any(x_[1] + "->" + x_[2] == PH for x_ in L_)]
    for (A2, B1), L in sorted(items_, key=lambda x: -len(x[1]))[:12]:
        Q, p1, p2, b1, a2, d = L[0]
        CURD[0] = RELD; dr = sepAny(A2, B1)[0]; CURD[0] = 0
        print("union %s->%s of %s (x%d): need Sep(%s -> %s) >= a-b = %d; depth0 %s; relative %s; leqP %s; t-gap %d" % (
            p1, p2, Q, len(L), s_(A2), s_(B1), a2 - b1, d, dr, bool(leqP(A2, B1)), el[B1][2] - el[A2][2]), flush=True)
th = threading.Thread(target=main); th.start(); th.join()
