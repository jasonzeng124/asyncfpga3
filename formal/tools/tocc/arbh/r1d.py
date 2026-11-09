"""Deep form-iv for the R1 pairs (UNTRUSTED). usage: r1d.py c
For each R1 pair (X = guard end E, Y = register re-open) from r1c_c<c>.pkl: over ALL common ancestors e0 (newest first),
Sep23(e0->Y) - Up(e0->X) as ao.py computes them (Up skips env events; CAUSEANC/PREVANC as default), the best value,
and for the e0 where Up fails, the first unbounded ancestor of X classified: ENV event / concurrent cause (not >= e0,
no Sep to e0) / other. Also: the env events and arbiter-q events that are common ancestors of X and Y."""
import sys, collections, pickle, json
c_ = sys.argv[1]; sys.argv = ["datal.py", c_]
src = open("/tmp/claude-0/arbh/datal.py").read(); src = src[:src.index("# ---------------- guards")]
exec(src)
an = open("/tmp/claude-0/arbh/r1an.py").read(); exec(an[an.index("ARBQ = {}"):an.index("roots = collections.defaultdict(list)")])
idn = {x: i for i, x in enumerate(nm)}
D = pickle.load(open("/tmp/claude-0/arbh/r1c_c%s.pkl" % c_, "rb"))["OUT"]
def first_block(e0, X, U):
    """earliest (topological) ancestor of X, at/after e0 in tm, not in U; classify"""
    anc = [e for e in ord_arr[int(tm[e0]):int(tm[X]) + 1] if (leqP(int(e), X) or int(e) == X)]
    for e in anc:
        e = int(e)
        if e in U or e == e0: continue
        v = el[e][0]
        if v in envnode: return "ENV " + en(e)
        if not leqP(e0, e):
            return "concurrent-with-e0 " + en(e)
        conc = [p for alt in alts[e] for p in alt if p not in U and not leqP(e0, p) and sep23(p, e0) is None]
        return "unbounded-cause %s (%s)" % (en(e), [en(p) for p in conc[:2]])
    return "?"
res = []
for d in D:
    if d["kind"] != "reopen": continue
    X = eid[(idn[d["X"][0]], d["X"][1])]; Y = eid[(idn[d["Y"][0]], d["Y"][1])]
    com = [e for e in range(NE) if leqP(e, X) and leqP(e, Y)]
    com.sort(key=lambda e: -tm[e])
    envc = [en(e) for e in com if el[e][0] in envnode]; arbc = [en(e) for e in com if nm[el[e][0]] in ARBQ]
    best = (-INF, None); nup = 0; why = collections.Counter(); ex = {}
    for e0 in com[:int(os.environ.get("NCAND", "400"))]:
        U = up_from(e0, int(tm[X]))
        s = sep23(e0, Y)
        if X in U:
            nup += 1
            if s is not None and s - U[X] > best[0]: best = (s - U[X], e0, s, U[X])
        else:
            w = first_block(e0, X, U); k = w.split(" ")[0]; why[k] += 1; ex.setdefault(k, (en(e0), w))
    need = None
    print("X=%s Y=%s gap %+d: common ancestors %d (ENV among them: %s; ARB: %d, newest %s)" % (en(X), en(Y), et[Y] - et[X], len(com), envc, len(arbc), arbc[:2]))
    print("   tried %d newest; Up(e0->X) exists for %d; best Sep23(e0->Y)-Up(e0->X) = %s %s" % (min(len(com), int(os.environ.get("NCAND", "400"))), nup, best[0],
          ("at e0=%s (Sep %d, Up %d)" % (en(best[1]), best[2], best[3])) if best[1] is not None else ""))
    print("   Up blocked:", dict(why), {k: v for k, v in ex.items()})
    res.append(dict(X=d["X"], Y=d["Y"], gap=int(et[Y] - et[X]), ncom=len(com), envc=envc, arbc=arbc[:4], nup=nup, best=best[0],
                    beste0=en(best[1]) if best[1] is not None else None, why=dict(why), ex=ex))
pickle.dump(res, open("/tmp/claude-0/arbh/r1d_c%s.pkl" % c_, "wb"))
