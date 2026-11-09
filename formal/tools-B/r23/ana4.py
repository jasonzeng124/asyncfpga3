#!/usr/bin/env python3
"""bsub1 (UNTRUSTED): root vs inherited truncations; for roots, why Sep(c2.A -> c1.B) and Up(c1.B -> c2.A) fail.
usage: ana4.py c -> ../trunc4_c<c>.json, ../trunc4_c<c>.txt"""
import sys, os, pickle, json, collections
c_ = sys.argv[1]
sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/bsub1/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
NEG = -INF
B0 = pickle.load(open("/tmp/claude-0/bsub1/tocc/datal_t_c%s.pkl" % c_, "rb")); MEMO = B0["MEMO"]
T3 = {(r["latch"], r["kind"], r["c1"][1], r["c2"][1]): r for r in json.load(open("/tmp/claude-0/bsub1/trunc3_c%s.json" % c_))}
def evs(e):
    if e is None: return None
    n, k, t = el[e]; return "%s(%d)@%d" % (nm[n], k, t)
def deeper(bind):
    out = []; seen = set()
    cur = MEMO.get(bind[2]) if bind and isinstance(bind, tuple) and len(bind) == 3 else None
    path = []
    while cur is not None and cur.get("key") not in seen:
        seen.add(cur.get("key")); path.append(nm[cur["key"][0]])
        if cur.get("kind") == "latch" and cur.get("trunc"):
            tr = cur["trunc"]; out.append((nm[tr["Q"]], tr["kind"], evs(tr["c1"]["B"]), evs(tr["c2"]["A"])))
        b = cur.get("bind")
        if not b or not isinstance(b, tuple) or len(b) != 3: break
        cur = MEMO.get(b[2])
    return out, path
def upblock(e0, e, U):
    seen = set(); steps = []
    for _ in range(400):
        if e in U: return ("reached Up set", e, steps)
        if e in seen: return ("loop", e, steps)
        seen.add(e); steps.append(evs(e))
        v, k, t = el[e]
        if v in envnode: return ("env event", e, steps)
        if tm[e] < tm[e0]: return ("non-common (not after e0, no Sep to e0)", e, steps)
        if k > 0 and prev[e] not in U and sep23(prev[e], e0) is None:
            e = prev[e]; continue
        best = None
        for alt in alts[e]:
            miss = [p for p in alt if p not in U and sep23(p, e0) is None]
            if best is None or len(miss) < len(best): best = miss
        if best is None: return ("no alternative", e, steps)
        if not best: return ("all causes ok (prev?)", e, steps)
        e = max(best, key=lambda p: tm[p])
    return ("depth", e, steps)
rows = {}
for tr in B0["TRUNC"]:
    c1, c2 = tr["c1"], tr["c2"]; A, Bd = c2["A"], c1["B"]
    k = (nm[tr["Q"]], tr["kind"], evs(Bd), evs(A))
    if k in rows: rows[k]["n"] += 1; continue
    dp, path = deeper(c1.get("bind"))
    r = dict(T3.get(k, {}))
    r.update(latch=k[0], kind=k[1], Dend=k[2], close=k[3], n=1, inherited_from=dp[:1], bindpath=path[:12],
             en=nm[tr["e"]], Dsrc=[nm[u] for j, u, w in tr["Dp"]])
    e = tr["e"]
    r["Dend_is_own_enable"] = el[Bd][0] == e if Bd is not None else None
    r["Dend_node_exact_in_D_cone_anchor"] = nm[el[Bd][0]] if Bd is not None else None
    if not dp:     # root: why
        if leqP(Bd, A):
            U = up_from(Bd, int(tm[A]))
            bl = upblock(Bd, A, U)
            r["why"] = "c1.B before c2.A causally; UnionOK needs Sep(c2.A->c1.B) >= 0: impossible; Up(c1.B->c2.A) " + ("= %d" % U[A] if A in U else "missing: " + bl[0] + " at " + evs(bl[1]))
            r["up_steps"] = bl[2][:8]
        elif leqP(A, Bd):
            r["why"] = "ordered c2.A <= c1.B: Sep finite %s" % r.get("sep_margin")
        else:
            m = np.minimum(VCP[A], VCP[Bd]); cands = []
            for x in np.nonzero(m)[0]:
                e0 = eid[(xs[x], int(m[x]) - 1)]
                if tm[e0] < tm[A]: cands.append((tm[e0], e0))
            cands.sort(reverse=True); ws = collections.Counter(); ex = []
            for _, e0 in cands[:10]:
                s = sep23(e0, Bd); U = up_from(e0, int(tm[A]))
                if A in U and s is not None: ws["Sep-Up finite"] += 1; continue
                if s is None: ws["no Sep e0->c1.B"] += 1
                if A not in U:
                    bl = upblock(e0, A, U); ws["Up e0->c2.A: " + bl[0]] += 1
                    if len(ex) < 2: ex.append((evs(e0), bl[0], evs(bl[1])))
            r["why"] = "unordered; common ancestors (10 latest): %s" % dict(ws); r["ex"] = ex
    rows[k] = r
R = sorted(rows.values(), key=lambda r: (bool(r["inherited_from"]), r["kind"], r["latch"]))
json.dump(R, open("/tmp/claude-0/bsub1/trunc4_c%s.json" % c_, "w"), indent=1, default=str)
o = open("/tmp/claude-0/bsub1/trunc4_c%s.txt" % c_, "w")
def P(*a): print(*a); print(*a, file=o)
P("[c=%s] distinct truncation events %d: root %d, inherited %d" % (c_, len(R), sum(1 for r in R if not r["inherited_from"]), sum(1 for r in R if r["inherited_from"])))
P("  roots by kind:", collections.Counter(r["kind"] for r in R if not r["inherited_from"]))
P("  roots by why-class:", collections.Counter((r["kind"], r["why"].split(":")[0] if "missing" not in r["why"] else r["why"].split(" at ")[0]) for r in R if not r["inherited_from"]).most_common())
for r in R:
    if r["inherited_from"]: continue
    P("ROOT %-16s %-5s en=%-16s Dend=%-30s close=%-30s ownEn=%s run_margin=%s sep_margin=%s up_direct=%s up_via_e0=%s\n      why: %s %s\n      D=%s bindpath=%s" % (
        r["latch"], r["kind"], r["en"], r["Dend"], r["close"], r["Dend_is_own_enable"], r.get("run_margin"), r.get("sep_margin"), r.get("up_direct"), r.get("up_via_e0"),
        r["why"], r.get("ex", r.get("up_steps", ""))[:4], r["Dsrc"], r["bindpath"][:6]))
