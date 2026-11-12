#!/usr/bin/env python3
"""bsub1: trace the U->H truncation of given latches: union terms, best form-iv e0, the Sep path e0->c1.B and the
Up path e0->c2.A (critical causes), arbiter nodes on them, and the D claim's end-binding chain.
usage: UPREL=1 trU.py c PKL LATCH..."""
import sys, os, pickle, collections
c_ = sys.argv[1]; PK = sys.argv[2]; LAT = sys.argv[3:]; sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/bsub1/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
M0 = pickle.load(open("/tmp/claude-0/bsub1/tocc/model.pkl", "rb")); idx = {n: i for i, n in enumerate(nm)}
ARBQ = set(idx[a["q"]] for a in M0["arbs"])
def E(e): n, k, t = el[e]; return "%s(%d)@%d%s" % (nm[n], k, t, "[ARB]" if n in ARBQ else "")
P = pickle.load(open(PK, "rb")); MEMO = P["MEMO"]
def sep_path(s, T):
    """reconstruct a forms-ii/iii path s -> T (backwards: the cause giving T's value)"""
    path = [T]; e = T
    while e != s and len(path) < 200:
        v = el[e][0]; best = None
        tgt = sep23(s, e)
        for alt in alts[e]:
            for p in alt:
                if sep23(s, p) is not None and sep23(s, p) + wlo(v, el[p][0]) >= tgt and (best is None or tm[p] > tm[best]): best = p
        if prev[e] is not None and sep23(s, prev[e]) is not None and sep23(s, prev[e]) + wlo(v, v) >= tgt and best is None: best = prev[e]
        if best is None: break
        path.append(best); e = best
    return path[::-1]
def up_path(e0, e):
    U = up_from(e0, int(tm[e])); path = [e]
    while e != e0 and len(path) < 200:
        v = el[e][0]; cands = []
        if el[e][1] > 0 and prev[e] in U: cands.append((U[prev[e]] + whi(v, v), prev[e], "prev"))
        for alt in alts[e]:
            for p in alt:
                if p in U: cands.append((U[p] + whi(v, el[p][0]), p, "cause"))
                else:
                    rb = relbound(p, e0) if sep23(p, e0) is None else None
                    path.append(("non-U cause %s: sep23->e0 %s rel %s" % (E(p), sep23(p, e0), rb)))
        if not cands: break
        x = max(cands); path.append(x[1]); e = x[1]
    return [E(p) if isinstance(p, (int, np.integer)) else p for p in path[::-1]]
done = set()
for tr in P["TRUNC"]:
    if nm[tr["Q"]] not in LAT or tr["kind"] != "U->H": continue
    c1, c2 = tr["c1"], tr["c2"]; B_, A_ = c1["B"], c2["A"]
    k = (tr["Q"], B_, A_)
    if k in done: continue
    done.add(k)
    print("=== %s U->H  c1.B=%s b=%d  c2.A=%s a=%d  run gap tau(c2.A)-tau(c1.B)=%d" % (nm[tr["Q"]], E(B_), c1["b"], E(A_), c2["a"], el[A_][2] - el[B_][2]))
    m = np.minimum(VCP[A_], VCP[B_]); cands = []
    for x in np.nonzero(m)[0]:
        e0 = eid[(xs[x], int(m[x]) - 1)]
        if tm[e0] < tm[A_]: cands.append((tm[e0], e0))
    cands.sort(reverse=True); best = None
    for _, e0 in cands[:10]:
        s = sep23(e0, B_); U = up_from(e0, int(tm[A_]))
        u = U.get(A_)
        print("   e0 %-40s Sep(e0->c1.B)=%s  Up(e0->c2.A)=%s  => union margin %s" % (E(e0), s, u, (c1["b"] + s - u - c2["a"]) if (s is not None and u is not None) else None))
        if s is not None and u is not None and (best is None or c1["b"] + s - u > best[0]): best = (c1["b"] + s - u, e0)
    if best:
        e0 = best[1]
        print("   Sep path e0 -> c1.B:", [E(p) for p in sep_path(e0, B_)])
        print("   Up path  e0 -> c2.A:", up_path(e0, A_))
    # D claim end binding
    b = c1.get("bind"); ch = []
    cur = MEMO.get(b[2]) if b and len(b) == 3 else None; seen = set()
    while cur is not None and cur.get("key") not in seen:
        seen.add(cur.get("key")); ch.append("%s[%s B=%s b=%s]" % (nm[cur["key"][0]], cur.get("kind"), E(cur["B"]) if cur.get("B") is not None else None, cur.get("b")))
        bb = cur.get("bind")
        if not bb or len(bb) != 3: ch.append("stop:%s" % (str(bb)[:40])); break
        cur = MEMO.get(bb[2])
    print("   D-claim end binding chain:", ch)
