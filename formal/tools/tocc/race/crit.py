# critical (last-arriving cause) chains from A=X22Y87.A6(0) and B=X27Y80.A6(2) back to the common past; usage crit.py c
import sys
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/race/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[n]: n for n in EX}
def E(n, k): return eid[(N[n], k)]
def s(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
A = E("SLICE_X22Y87.A6", 0); B = E("SLICE_X27Y80.A6", 2)
def mid(v, w): return dl[(v, w)][2] if (v, w) in dl else 1
def chain(x, other):
    out = [x]
    while not leqP(x, other):
        v = el[x][0]; cands = set(p for alt in alts[x] for p in alt)
        if prev[x] is not None: cands.add(prev[x])
        if not cands: break
        p = max(cands, key=lambda p: et[p] + (mid(v, el[p][0]) if el[p][0] != v else 0))
        out.append(p); x = p
    return out
res = {}
for name, x, o in (("A", A, B), ("B", B, A)):
    ch = chain(x, o); res[name] = ch
    print("chain %s (c=%s):" % (name, cc))
    slo = shi = 0
    for i, e in enumerate(ch):
        if i + 1 < len(ch):
            p = ch[i + 1]; v = el[e][0]; w = el[p][0]
            lo, hi, md = dl.get((v, w), (1, 1, 1)) if v != w else (dl.get((v, v), (1, 1, 1)))
            if v in envnode: lo, hi, md = 1, None, 1
            slo += lo; shi += (hi if hi is not None else float("inf"))
            print("   %-32s <- %-32s pin win [%s,%s] mid %s, gap %d, alts %d" % (s(e), s(p), lo, hi, md, et[e] - et[p], len(alts[e])))
        else: print("   %s  [common ancestor: below %s]" % (s(e), "B" if name == "A" else "A"))
    print("   sum lo %d  sum hi %s  sim %d" % (slo, shi, et[ch[0]] - et[ch[-1]]))
import pickle; pickle.dump(dict(A=[el[e] for e in res["A"]], B=[el[e] for e in res["B"]]), open("/tmp/claude-0/race/crit_c%s.pkl" % cc, "wb"))
# relation of the two roots
ra, rb = res["A"][-1], res["B"][-1]
print("roots", s(ra), s(rb), "ra<=rb", bool(leqP(ra, rb)), "rb<=ra", bool(leqP(rb, ra)), "sep23(ra,rb)", sep23(ra, rb), "sep23(rb,ra)", sep23(rb, ra))
print("sep23(ra->B) %s, sep23(ra->A) %s, sep23(rb->A) %s, sep23(rb->B) %s" % (sep23(ra, B), sep23(ra, A), sep23(rb, A), sep23(rb, B)))
