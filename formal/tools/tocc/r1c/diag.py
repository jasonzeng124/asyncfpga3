# why Up(e0 -> E) fails with the relative clause: the blocker chain (R1 pair, c=1)
import sys, time
sys.argv = ["ao.py", sys.argv[1] if len(sys.argv) > 1 else "1", "0"]
src = open("/tmp/claude-0/r1c/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
exec(open("/tmp/claude-0/r1c/relup.py").read())
import os
r = {nm[n]: n for n in EX}
def ev_(s): n, k = s.rsplit("(", 1); return eid[(r[n], int(k[:-1]))]
E = ev_(os.environ.get("EE", "SLICE_X39Y47.D6(1)")); B = ev_(os.environ.get("BB", "SLICE_X30Y76.A6(2)"))
D = int(os.environ.get("DD", "1"))
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
m = np.minimum(VCP[E], VCP[B]); cands = []
for x in np.nonzero(m)[0]:
    e0 = eid[(xs[x], int(m[x]) - 1)]
    if tm[e0] < tm[E]: cands.append((tm[e0], e0))
cands.sort(reverse=True)
def blk(e0, e, depth, ind, seen):
    if e in seen or len(seen) > 40: return
    seen.add(e)
    v, k, t = el[e]
    if v in envnode or v not in g: print(ind + "ENV/non-gate", s_(e)); return
    U = _extend(e0, depth, int(tm[e]))["U"]
    bad = []
    if k > 0 and _term(prev[e], e0, depth, U, whi(v, v)) is None: bad.append(("prev", prev[e]))
    altbad = []
    for alt in alts[e]:
        b_ = [p for p in alt if _term(p, e0, depth, U, whi(v, el[p][0])) is None]
        altbad.append(b_)
    print(ind + s_(e), "prev blocked" if bad else "", "alts blocked:", [[s_(p) + ("<e0" if tm[p] < tm[e0] else "") + (" below-e0" if leqP(p, e0) else "") for p in b] for b in altbad])
    nxt = [p for _, p in bad] + (min(altbad, key=len) if altbad and all(altbad) else [])
    for p in nxt[:3]:
        if tm[p] >= tm[e0]: blk(e0, p, depth, ind + "  ", seen)
        else:
            an = _anchors(p, e0)[:RELTRY]
            info = [(s_(a), sep23(a, e0), up_get(a, p, depth - 1) if depth > 0 else "-") for a in an[:6]]
            print(ind + "  concurrent-before-e0", s_(p), "anchors(a, Sep23 a->e0, Up a->p):", info)
for _, e0 in cands[:3]:
    print("== e0", s_(e0), "Sep23(e0->B)", sep23(e0, B), "Up(e0->E) depth", D, up_get(e0, E, D))
    if up_get(e0, E, D) is None: blk(e0, E, D, "  ", set())
