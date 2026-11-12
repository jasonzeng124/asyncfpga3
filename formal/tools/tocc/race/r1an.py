"""R1 analysis (UNTRUSTED). usage: r1an.py c   (runs datal.py up to the loop-cover section with its default NPASS)
For each failing guard: root end event B (as m8.py), class R1 if B fires after E in the run (gap > 0).
For each R1 (E, B): critical causal chains back from E and from B to the first common ancestor (leqP), tags on each
event (ENV kind / ARB q / OR n-alts), and for each maximal common ancestor e0: does Sep23(e0->B) exist, does Up(e0->E)
exist, and if not, the first event on E's critical chain that up_from(e0) cannot bound, and why."""
import sys, os, collections, pickle
c_ = sys.argv[1]
sys.argv = ["datal.py", c_]
src = open("/tmp/claude-0/race/datal.py").read(); src = src[:src.index("# ---------------- loop covers")]
exec(src)
import json
ARBQ = {}
for i, a in enumerate(json.load(open("/tmp/claude-0/race/bnd.json"))["arbs"]):
    ARBQ[a["q"]] = i
def tag(e):
    v, k, t = el[e]; s = []
    if v in envnode: s.append("ENV:%s" % envnode[v])
    if nm[v] in ARBQ: s.append("ARB%d" % ARBQ[nm[v]])
    if v in g and len(alts[e]) > 1: s.append("OR%d" % len(alts[e]))
    return s
def en(e): return "%s(%d)@%d%s" % (nm[el[e][0]], el[e][1], el[e][2], ("[" + ",".join(tag(e)) + "]") if tag(e) else "")
def firing_alt(e):
    if not alts[e]: return []
    return min(alts[e], key=lambda a: max([et[p] for p in a], default=-1))
def crit_chain(e, other):
    """walk back from e along the latest cause (firing alternative or prev) until an event <= other"""
    ch = [e]; x = e
    while not leqP(x, other) and x != other:
        cs = list(firing_alt(x)) + ([prev[x]] if prev[x] is not None else [])
        if not cs: break
        x = max(cs, key=lambda p: et[p]); ch.append(x)
    return ch[::-1]
def maximal_common(E, B):
    m = np.minimum(VCP[E], VCP[B])
    cs = [eid[(xs[x], int(m[x]) - 1)] for x in np.nonzero(m)[0]]
    mx = [a for a in cs if not any(b_ != a and leqP(a, b_) for b_ in cs)]
    return sorted(mx, key=lambda e_: -et[e_])
def why_no_up(e0, E, chain):
    U = up_from(e0, int(tm[E]))
    if E in U: return "Up(e0->E) = %d" % U[E], None
    # first event on chain after e0 that is not in U
    if e0 not in chain:
        return "E's critical chain does not pass through e0 (it starts at %s, an ancestor of e0); E is reached from e0 only via other causes; first unbounded on chain after start: %s" % (en(chain[0]), next((en(x) for x in chain[1:] if x not in U), None)), None
    i0 = chain.index(e0)
    for x in chain[i0 + 1:]:
        if x in U: continue
        v = el[x][0]
        if v in envnode: return "blocked at ENV event %s" % en(x), x
        if v not in g: return "blocked at non-gate %s" % en(x), x
        if el[x][1] > 0 and prev[x] not in U and sep23(prev[x], e0) is None:
            return "blocked at %s: previous event %s neither bounded nor before e0" % (en(x), en(prev[x])), x
        bad = []
        for alt in alts[x]:
            miss = [p for p in alt if p not in U and sep23(p, e0) is None]
            bad.append([en(p) for p in miss])
        return "blocked at %s: every alternative has an unbounded cause: %s" % (en(x), bad), x
    return "E not in U but chain all bounded (chain not through e0?)", None
roots = collections.defaultdict(list)
fails = []
for x in G_:
    if len(x) != 7: continue
    v, z, ms, me, cz, st, en_ = x
    if min(ms, me) >= 0: continue
    if en_ is None or me >= 0: roots[("start", None)].append(x); continue
    E = eid[en_]
    stack = [cz["key"]]; seen = set(); rb = set()
    while stack:
        k = stack.pop()
        if k in seen: continue
        seen.add(k)
        w = memo.get(k)
        if not isinstance(w, dict) or w["B"] is None or sep(E, w["B"]) != NEG: continue
        kids = [k2 for u, k2 in w.get("cov", []) if k2 is not None and isinstance(memo.get(k2), dict) and memo[k2]["B"] == w["B"]]
        if kids: stack += kids
        else: rb.add((w["B"], k[0], w["kind"]))
    for B, owner, kind in rb:
        fails.append(dict(v=v, z=z, E=E, B=B, owner=owner, kind=kind, gap=int(et[B] - et[E]), st=st, en=en_, claimB=cz["B"]))
print("PER-GUARD: v z E claimB gapClaimB | roots(B gap owner kind)")
for x in G_:
    if len(x) != 7 or min(x[2], x[3]) >= 0: continue
    v, z, ms, me, cz, st, en_ = x
    if en_ is None or me >= 0: print("  start-side", nm[v], nm[z]); continue
    E = eid[en_]; cb = cz["B"]
    rs = [(f["B"], f["gap"], nm[f["owner"]], f["kind"]) for f in fails if f["v"] == v and f["z"] == z and f["st"] == st and f["en"] == en_]
    print("  %s z=%s S=%s(%d) E=%s claimB=%s gap %+d | %s" % (nm[v], nm[z], nm[st[0]], st[1], en(E), en(cb) if cb is not None else None, (et[cb]-et[E]) if cb is not None else 0,
          sorted(set((en(b), gp, o, k) for b, gp, o, k in rs), key=lambda r: -r[1])[:4]))
nf = sum(1 for x in G_ if len(x) == 7 and min(x[2], x[3]) < 0)
print("[c=%s] failing guards %d (root (E,B) records %d)" % (c_, nf, len(fails)))
R1 = [f for f in fails if f["gap"] > 0]
gids = set((f["v"], f["z"], f["st"], f["en"]) for f in R1)
print("R1 (root end B after E in the run): %d guards, %d records; others: %d guards" % (
    len(gids), len(R1), len(set((f["v"], f["z"], f["st"], f["en"]) for f in fails if f["gap"] <= 0))))
pairs = collections.defaultdict(list)
for f in R1: pairs[(f["E"], f["B"])].append(f)
out = []
for (E, B), fl in sorted(pairs.items(), key=lambda kv: -len(kv[1])):
    f = fl[0]
    print("\n=== E=%s  B=%s  gap %+d ps  [%d guard records; e.g. reader %s z %s, B ends claim of %s (%s)]" % (
        en(E), en(B), f["gap"], len(fl), nm[f["v"]], nm[f["z"]], nm[f["owner"]], f["kind"]))
    print("    readers/z:", sorted(set((nm[x["v"]], nm[x["z"]]) for x in fl)))
    mc = maximal_common(E, B)
    chE = crit_chain(E, B); chB = crit_chain(B, E)
    print("    maximal common ancestors (%d): %s" % (len(mc), [en(e_) for e_ in mc[:6]]))
    print("    chain to E (%d ev):" % len(chE), " -> ".join(en(e_) for e_ in chE))
    print("    chain to B (%d ev):" % len(chB), " -> ".join(en(e_) for e_ in chB))
    envE = [en(e_) for e_ in chE[1:] if el[e_][0] in envnode]; envB = [en(e_) for e_ in chB[1:] if el[e_][0] in envnode]
    arbE = [en(e_) for e_ in chE if nm[el[e_][0]] in ARBQ]; arbB = [en(e_) for e_ in chB if nm[el[e_][0]] in ARBQ]
    print("    env on E-chain: %s; env on B-chain: %s; arb on E-chain: %s; arb on B-chain: %s" % (envE, envB, arbE, arbB))
    res = []
    for e0 in mc[:4]:
        s = sep23(e0, B)
        w, blk = why_no_up(e0, E, crit_chain(E, e0) if leqP(e0, E) else chE)
        res.append((en(e0), s, w))
        print("    e0=%s: Sep23(e0->B)=%s; %s" % (en(e0), s, w))
    out.append(dict(E=(nm[el[E][0]], el[E][1], int(et[E])), B=(nm[el[B][0]], el[B][1], int(et[B])), gap=f["gap"],
                    n=len(fl), guards=sorted(set((nm[x["v"]], nm[x["z"]], nm[el[eid[x["st"]]][0]], x["st"][1]) for x in fl)),
                    chE=[en(e_) for e_ in chE], chB=[en(e_) for e_ in chB], envE=envE, envB=envB, arbE=arbE, arbB=arbB, mc=res,
                    owner=nm[f["owner"]], kind=f["kind"]))
pickle.dump(dict(R1=out, nonR1=[(nm[f["v"]], nm[f["z"]], nm[el[f["E"]][0]], nm[el[f["B"]][0]], f["gap"]) for f in fails if f["gap"] <= 0]),
            open("/tmp/claude-0/race/r1an_c%s.pkl" % c_, "wb"))
