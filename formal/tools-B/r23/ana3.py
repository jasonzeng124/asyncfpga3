#!/usr/bin/env python3
"""bsub1 (UNTRUSTED): for every distinct truncation event of the base datal_t run, the alternative bounds that
could close the union c1 -> c2 (need tau(c2.A) + c2.a <= tau(c1.B) + c1.b):
 * lower Sep(c2.A -> c1.B) (what datal/Lean UnionOK use)            margin = c1.b + Sep - c2.a
 * upper Up(c1.B -> c2.A) when c1.B precedes c2.A causally           margin = c1.b - Up - c2.a
 * via a common ancestor e0: Up(e0 -> c2.A) - Sep(e0 -> c1.B)         margin = c1.b - (Up - Sep) - c2.a
 * the simulated run                                                 margin = c1.b - (t(c2.A) - t(c1.B)) - c2.a
usage: ana3.py c   -> ../trunc3_c<c>.json"""
import sys, os, pickle, json, collections
c_ = sys.argv[1]
sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/bsub1/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
NEG = -INF
B0 = pickle.load(open("/tmp/claude-0/bsub1/tocc/datal_t_c%s.pkl" % c_, "rb"))
def evs(e):
    if e is None: return None
    n, k, t = el[e]; return "%s(%d)@%d" % (nm[n], k, t)
seen = {}
for tr in B0["TRUNC"]:
    c1, c2 = tr["c1"], tr["c2"]; A, Bd = c2["A"], c1["B"]
    k = (nm[tr["Q"]], tr["kind"], Bd, A)
    if k in seen: seen[k]["n"] += 1; continue
    r = dict(latch=nm[tr["Q"]], kind=tr["kind"], en=nm[tr["e"]], c1=(c1["ph"], evs(Bd), c1["b"]), c2=(c2["ph"], evs(A), c2["a"]), n=1)
    s = sepAny(A, Bd)[0]
    r["sep_margin"] = None if s == NEG else c1["b"] + s - c2["a"]
    r["order"] = "c1.B<=c2.A" if leqP(Bd, A) else ("c2.A<=c1.B" if leqP(A, Bd) else "unordered")
    r["run_margin"] = int(c1["b"] - (et[A] - et[Bd]) - c2["a"])
    r["up_direct"] = None
    if leqP(Bd, A):
        U = up_from(Bd, int(tm[A]))
        if A in U: r["up_direct"] = int(c1["b"] - U[A] - c2["a"])
    best = None; bestw = None
    m = np.minimum(VCP[A], VCP[Bd]); cands = []
    for x in np.nonzero(m)[0]:
        for back in (1, 2):
            if int(m[x]) - back < 0: continue
            e0 = eid[(xs[x], int(m[x]) - back)]; cands.append((tm[e0], e0))
    cands.sort(reverse=True)
    for _, e0 in cands[:15]:
        s0_ = sep23(e0, Bd)
        if s0_ is None: continue
        U = up_from(e0, int(tm[A]))
        if A not in U: continue
        mm = c1["b"] - (U[A] - s0_) - c2["a"]
        if best is None or mm > best: best = int(mm); bestw = evs(e0)
    r["up_via_e0"] = best; r["e0"] = bestw
    seen[k] = r
rows = list(seen.values())
json.dump(rows, open("/tmp/claude-0/bsub1/trunc3_c%s.json" % c_, "w"), indent=1)
def cls(r):
    if r["sep_margin"] is not None: return "Sep finite, short"
    if r["up_direct"] is not None and r["up_direct"] >= 0: return "anchor before close, Up closes it"
    if r["up_via_e0"] is not None and r["up_via_e0"] >= 0: return "unordered/anchor, Up-Sep via e0 closes it"
    if r["up_direct"] is not None or r["up_via_e0"] is not None: return "Up bound exists but too large"
    return "no bound either way"
C = collections.Counter((r["kind"], r["order"], cls(r)) for r in rows)
print("[c=%s] %d distinct truncation events" % (c_, len(rows)))
for k, n in sorted(C.items()): print("  %4d %s" % (n, k))
print("  run margins < 0:", [(r["latch"], r["kind"], r["run_margin"]) for r in rows if r["run_margin"] < 0][:20])
