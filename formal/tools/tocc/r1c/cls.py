# classify failing guards of a datal pickle: E, claim.B, time gap, causal relation, Sep23
import sys, os, pickle, collections
cc = sys.argv[1]; pk = sys.argv[2]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/r1c/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
D = pickle.load(open(pk, "rb")); G = D["G"]
cls = collections.Counter(); rows = []
for x in G:
    if len(x) != 7: cls["cycle"] += 1; continue
    v, z, ms, me, cz, st, en_ = x
    if min(ms, me) >= 0: continue
    E = eid[en_] if en_ else None; B = cz["B"]
    if E is None or B is None: k = "E or B none"
    else:
        gap = el[B][2] - el[E][2]
        if leqP(E, B): k = "B causally after E (sep23 %s)" % ("none" if sep23(E, B) is None else "ok")
        elif leqP(B, E): k = "B causally BEFORE E (claim end too early)"
        else: k = "unordered, B %s E in time" % ("after" if gap > 0 else "before")
    cls[(k, nm[el[B][0]] if B is not None else None)] += 1
    rows.append((nm[v], nm[z], s_(E) if E is not None else None, s_(B) if B is not None else None, k))
for k, n in cls.most_common(): print("%4d %s" % (n, k))
for r in rows: print("   ", r)
