import sys, os
os.environ["UPREL"] = "1"
c_ = sys.argv[1]; sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/bsub1/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
idx = {n: i for i, n in enumerate(nm)}
def E(n, k): return eid[(idx[n], k)]
def upblock(e0, e, U):
    seen = set(); steps = []
    for _ in range(400):
        if e in U: return ("reached", steps)
        if e in seen: return ("loop", steps)
        seen.add(e); v, k, t = el[e]; steps.append("%s(%d)@%d" % (nm[v], k, t))
        if v in envnode: return ("env", steps)
        if k > 0 and prev[e] not in U and sep23(prev[e], e0) is None and relbound(prev[e], e0) is None:
            e = prev[e]; continue
        best = None
        for alt in alts[e]:
            miss = [p for p in alt if p not in U and sep23(p, e0) is None and relbound(p, e0) is None]
            if best is None or len(miss) < len(best): best = miss
        if best is None: return ("noalt", steps)
        if not best: return ("all ok?", steps)
        e = max(best, key=lambda p: tm[p])
    return ("depth", steps)
for a, b in [(("SLICE_X34Y92.A6", 0), ("SLICE_X34Y92.A6", 1))]:
    e0, e = E(*a), E(*b); U = up_from(e0, int(tm[e]))
    print(a, b, "Up:", U.get(e), "|U|", len(U))
    r = upblock(e0, e, U); print(r[0], r[1][:12])
    p = E("SLICE_X11Y25.B6", 2); print("relbound X11Y25.B6(2) vs e0:", relbound(p, e0), "sep23", sep23(p, e0), "leqP", leqP(p, e0), leqP(e0, p))
    m = np.minimum(VCP[p], VCP[e0]); nzx = np.nonzero(m)[0]; evs_ = EBASE[nzx] + m[nzx] - 1
    evs_ = evs_[np.argsort(-tm[evs_])][:8]
    for a_ in evs_.tolist():
        U0 = up_from(a_, int(tm[p]), rel=False)
        print("   base", nm[el[a_][0]], el[a_][1], el[a_][2], "sep23(a,e0)", sep23(a_, e0), "Up0(a->p)", U0.get(p), "blk", upblock(a_, p, U0)[1][:4] if p not in U0 else "")
e0 = E("SLICE_X34Y92.A6", 0); e = E("SLICE_X34Y92.A6", 1); U = up_from(e0, int(tm[e]))
def why(e, depth=0):
    v, k, t = el[e]
    parts = []
    if k > 0:
        pp = prev[e]; parts.append(("prev", "%s(%d)@%d" % (nm[el[pp][0]], el[pp][1], el[pp][2]), U.get(pp), sep23(pp, e0), relbound(pp, e0)))
    for alt in alts[e]:
        parts.append([("%s(%d)@%d" % (nm[el[p][0]], el[p][1], el[p][2]), U.get(p), sep23(p, e0), relbound(p, e0), whi(v, el[p][0])) for p in alt])
    print("  " * depth, "%s(%d)@%d U=%s" % (nm[v], k, t, U.get(e)), parts)
    return parts
cur = e
for d in range(12):
    parts = why(cur, d)
    # follow the cause with the largest U among the best alt
    cand = [(U.get(p, -1), p) for alt in alts[cur] for p in alt if p in U]
    if cur and el[cur][1] > 0 and prev[cur] in U: cand.append((U[prev[cur]], prev[cur]))
    if not cand: break
    cur = max(cand)[1]
    if cur == e0: break
