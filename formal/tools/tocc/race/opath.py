# longest-lo (Sep23) path from X in {A, B} to the reader opens O = X24Y77.A6(2), O2 = X26Y85.A6(2); usage opath.py c
import sys
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/race/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[n]: n for n in EX}
def E(n, k): return eid[(N[n], k)]
def s(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
A = E("SLICE_X22Y87.A6", 0); B = E("SLICE_X27Y80.A6", 2)
for X, xn in ((A, "A"), (B, "B")):
    for T in (E("SLICE_X24Y77.A6", 2), E("SLICE_X26Y85.A6", 2)):
        path = [T]; x = T
        while x != X:
            v = el[x][0]; best = None
            for alt in alts[x]:
                for p in alt:
                    sp = sep23(X, p)
                    if sp is not None and (best is None or sp + wlo(v, el[p][0]) > best[0]): best = (sp + wlo(v, el[p][0]), p)
            if prev[x] is not None and sep23(X, prev[x]) is not None:
                sp = sep23(X, prev[x]) + wlo(v, v)
                if best is None or sp > best[0]: best = (sp, prev[x])
            x = best[1]; path.append(x)
        print("c=%s %s -> %s: Sep %d via %s" % (cc, xn, s(T), sep23(X, T), " <- ".join("%s(%d)" % (nm[el[e][0]], el[e][1]) for e in path)))
