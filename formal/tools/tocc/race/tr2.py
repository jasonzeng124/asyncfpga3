# list H->U' truncations of a datal pickle with the D input's own last change before the re-open
import sys, os, pickle, collections
cc = sys.argv[1]; pk = sys.argv[2]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/race/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2]) if e is not None else None
T = pickle.load(open(pk, "rb"))["TRUNC"]
cnt = collections.Counter((p1, p2) for (Q, p1, p2, *_ ) in T); print(cnt)
for (Q, p1, p2, A2, B1, b1, a2, d) in T:
    if (p1, p2) != ("H", "U'"): continue
    fb, en = C["LATCH"][Q]
    Dp = [p["src"] for j, p in enumerate(g[Q]["pins"]) if p["live"] and j not in fb and p["src"] not in C["const"] and p["src"] not in EX]
    ln = []
    for u in Dp:
        f = hist[u][1] if u in hist else []
        ln.append((nm[u], "EX" if u in EX else ("L" if u in C["LATCH"] else "comb"), [x for x in f if x <= el[B1][2]][-1:] ))
    print(nm[Q], "U'.A", s_(A2), "a", a2, "H.B", s_(B1), "b", b1, "d", d, ln)
