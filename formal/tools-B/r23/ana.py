#!/usr/bin/env python3
"""bsub1 (UNTRUSTED): truncation events of datal_t.py, diagnosis of each failing union, guard attribution.
usage: ana.py c   (reads datal_t_c<c>.pkl, dt_nouh_c<c>.pkl, dt_noall_c<c>.pkl if present; writes trunc_c<c>.json/.txt)"""
import sys, os, pickle, json, collections
c_ = sys.argv[1]
sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/bsub1/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
D = "/tmp/claude-0/bsub1/tocc/"
B0 = pickle.load(open(D + "datal_t_c%s.pkl" % c_, "rb"))
def ld(f):
    try: return pickle.load(open(D + f, "rb"))
    except Exception: return None
NUH = ld("dt_nouh_c%s.pkl" % c_); NALL = ld("dt_noall_c%s.pkl" % c_)
MEMO = B0["MEMO"]; NEG = -INF
def evs(e):
    if e is None: return None
    n, k, t = el[e]; return "%s(%d)@%d" % (nm[n], k, t)
def flips(n): return hist[n][1] if n in hist else []
def nextflip(n, t):
    for x in flips(n):
        if x > t: return x
    return None
def gkey(x): v, z, ms, me, cz, st, en_ = x; return (nm[v], nm[z], st, en_)
def failing(P):
    return {gkey(x): x for x in P["G"] if len(x) == 7 and min(x[2], x[3]) < 0}
F0 = failing(B0); FU = failing(NUH) if NUH else None; FA = failing(NALL) if NALL else None
# ---- Up blocker
def upblock(e0, e, U, depth=0):
    seen = set()
    while depth < 200:
        depth += 1
        if e in U: return ("in Up", e)
        if e in seen: return ("loop", e)
        seen.add(e)
        v, k, t = el[e]
        if v in envnode: return ("env event", e)
        if v not in g: return ("non-gate", e)
        if tm[e] < tm[e0]: return ("non-common (before e0, no Sep to e0)", e)
        if k > 0 and prev[e] not in U and sep23(prev[e], e0) is None:
            e = prev[e]; continue
        best = None
        for alt in alts[e]:
            miss = [p for p in alt if p not in U and sep23(p, e0) is None]
            if best is None or len(miss) < len(best): best = miss
        if best is None: return ("no alternative", e)
        if not best: return ("in Up?", e)
        e = max(best, key=lambda p: tm[p])
    return ("depth", e)
def diag(A, B):
    """why Sep(A -> B) is missing or small: (class, detail)"""
    s23 = sep23(A, B); f, e0 = form4(A, B)
    if leqP(A, B):
        return ("ordered A<=B (path sum)", dict(sep23=s23, form4=f))
    if leqP(B, A):
        return ("REVERSED: D end causally before close", {})
    m = np.minimum(VCP[A], VCP[B]); cands = []
    for x in np.nonzero(m)[0]:
        e0_ = eid[(xs[x], int(m[x]) - 1)]
        if tm[e0_] < tm[A]: cands.append((tm[e0_], e0_))
    cands.sort(reverse=True)
    rs = []
    for _, e0_ in cands[:10]:
        s = sep23(e0_, B)
        U = up_from(e0_, int(tm[A]))
        if A in U: rs.append((evs(e0_), "Sep %s Up %s" % (s, U[A]), s - U[A] if s is not None else None, None)); continue
        bl = upblock(e0_, A, U)
        rs.append((evs(e0_), "Sep %s, no Up" % s, None, (bl[0], evs(bl[1]))))
    if not cands: return ("unordered, no common ancestor", {})
    if f > -INF: return ("unordered, form iv margin finite", dict(form4=f, via=evs(e0), cands=rs))
    blk = collections.Counter(r[3][0] for r in rs if r[3])
    nosep = sum(1 for r in rs if r[1].startswith("Sep None"))
    cls = "unordered, Up blocked: " + (blk.most_common(1)[0][0] if blk else "?")
    return (cls, dict(cands=rs, nosep=nosep))
# ---- events
T = B0["TRUNC"]
rows = {}
for tr in T:
    Q = tr["Q"]; c1, c2 = tr["c1"], tr["c2"]
    k = (nm[Q], tr["kind"], c1["B"], c2["A"])
    r = rows.get(k)
    if r is None:
        e = tr["e"]; emd = tr["emd"]
        close = c2["A"]
        cls, det = diag(c2["A"], c1["B"])
        dps = []
        for j, u, w in tr["Dp"]:
            tc = (et[close] + emd) if tr["kind"] == "U->H" else None
            nf = nextflip(u, tc - w[2]) if tc is not None else None
            dps.append(dict(pin=j, src=nm[u], exact=(u in EX), win=list(w), next_flip=nf,
                            next_at_pin=(nf + w[2]) if nf is not None else None,
                            gap=(nf + w[2] - tc) if nf is not None else None))
        r = rows[k] = dict(latch=nm[Q], kind=tr["kind"], en=nm[e], en_win=[tr["elo"], tr["ehi"], emd],
                           c1=dict(ph=c1["ph"], B=evs(c1["B"]), b=c1["b"]), c2=dict(ph=c2["ph"], A=evs(c2["A"]), a=c2["a"]),
                           d=(None if tr["d"] == NEG else tr["d"]), margin=(None if tr["margin"] == NEG else tr["margin"]),
                           cls=cls, det=det, Dp=dps, val=tr["val"], n=0, guards=set(),
                           runtime_gap=(int(et[c1["B"]] - et[c2["A"]]) if c1["B"] is not None and c2["A"] is not None else None))
    r["n"] += 1
# ---- guard attribution through end-binding chains
def trace(cz):
    out = []; cur = MEMO.get(cz.get("key")) or cz; seen = set()
    while cur is not None:
        if cur.get("key") in seen: break
        seen.add(cur.get("key"))
        if cur.get("kind") == "latch" and cur.get("trunc"):
            tr = cur["trunc"]; out.append((nm[tr["Q"]], tr["kind"], tr["c1"]["B"], tr["c2"]["A"]))
        b = cur.get("bind")
        if not b or not isinstance(b, tuple) or len(b) != 3: break
        cur = MEMO.get(b[2])
    return out
gattr = collections.defaultdict(list)
for gk, x in F0.items():
    for t_ in trace(x[4]): gattr[gk].append(t_)
for gk, lst in gattr.items():
    for t_ in lst:
        if t_ in rows: rows[t_]["guards"].add(gk)
res = []
for k, r in rows.items():
    gs = sorted(r["guards"], key=str)
    r["guards_n"] = len(gs)
    r["guards_fixed_by_noUH"] = sum(1 for gk in gs if FU is not None and gk not in FU)
    r["guards_fixed_by_noall"] = sum(1 for gk in gs if FA is not None and gk not in FA)
    r["guards"] = ["%s z=%s E=%s" % (gk[0], gk[1], gk[3]) for gk in gs]
    res.append(r)
res.sort(key=lambda r: (-r["guards_n"], r["kind"], r["latch"]))
json.dump(dict(c=c_, nfail=len(F0), nfail_noUH=(len(FU) if FU is not None else None), nfail_noall=(len(FA) if FA is not None else None),
               fixed_noUH=sorted(map(str, set(F0) - set(FU))) if FU is not None else None,
               new_noUH=sorted(map(str, set(FU) - set(F0))) if FU is not None else None,
               guards_no_trunc_on_path=sum(1 for gk in F0 if not gattr.get(gk)), rows=res),
          open(D + "../trunc_c%s.json" % c_, "w"), indent=1, default=str)
# ---- text summary
o = open(D + "../trunc_c%s.txt" % c_, "w")
def P(*a): print(*a); print(*a, file=o)
P("[c=%s] failing guards: base %d, no U->H truncation %s, no truncation at all %s" % (c_, len(F0), len(FU) if FU is not None else "?", len(FA) if FA is not None else "?"))
P("  failing guards with a truncated latch on their claim-end binding chain: %d" % sum(1 for gk in F0 if gattr.get(gk)))
kc = collections.Counter(); kn = collections.Counter(); kl = collections.defaultdict(set)
for r in res: kc[r["kind"]] += r["n"]; kn[r["kind"]] += 1; kl[r["kind"]].add(r["latch"])
for k in kc: P("  kind %-6s: %d claim builds truncated, %d distinct (latch, D-end, close) events, %d distinct latches" % (k, kc[k], kn[k], len(kl[k])))
P("  U->H classes:", collections.Counter(r["cls"] for r in res if r["kind"] == "U->H").most_common())
P("  all classes by kind:", collections.Counter((r["kind"], r["cls"]) for r in res).most_common())
for r in res:
    if r["kind"] != "U->H" and r["guards_n"] == 0: continue
    P("%-16s %-6s en=%-16s close=%-32s Dend=%-32s gap=%s margin=%s cls=%s guards=%d (fixed noUH %d) D=%s" % (
        r["latch"], r["kind"], r["en"], r["c2"]["A"], r["c1"]["B"], r["runtime_gap"], r["margin"], r["cls"], r["guards_n"], r["guards_fixed_by_noUH"],
        [(d["src"], d["gap"]) for d in r["Dp"]]))
o.close()
