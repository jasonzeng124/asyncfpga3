#!/usr/bin/env python3
"""Shard C (UNTRUSTED): mux-aware data claims in the shape of TimedOccX/TimedOccU, and GuardTime for every guard.
Claims are built on demand, one per (node, simulated stable interval of that node), guided by the simulated run:
* operand bus bits: claim A = B = none (hEnvC, one pair); nodes never changed since power-up and before t0: A = none
  for the part before t0 (hInit);
* data comb gate z: pins whose simulated value is constant over z's read interval are candidates for cover (exact
  pin: Cov.ex between two of its events; data pin: Cov.cl by the pin's own claim), all others Cov.X; covered pins are
  then dropped greedily to X while the LUT output stays definite (ValOK checked exhaustively over the X pins); the
  claim's (A, a) and (B, b) are chosen among the covered pins' windows so that every CovTime inequality holds with
  Sep (d from the AO Sep: forms ii/iii + iv); a missing Sep or a negative b is a failure;
* data latch Q = en ? D : Q (one exact enable): a chain (ChainOK) of phase claims: transparent T (en Cov.ex active,
  D covered, feedback X), uncertain U (en X, D covered, feedback covered by the union claim itself: ValOK because
  both agree), hold H (en Cov.ex inactive, feedback by the union), repeated while the value is re-latched; union
  conditions next.a <= prev.b + Sep(next.A -> prev.B) are obligations (the U->H one is the latch hold condition);
  a value from before t0 starts with an H phase with A = none (hInit);
* guards: GuardTime for the claim of z that contains the guard's read interval.
Every inequality is recorded with its margin.  usage: datal.py c   (PAIR env selects the operand pair)"""
import sys, pickle, collections, os, itertools
from bisect import bisect_right
c_ = sys.argv[1]
sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/r1c/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
exec(open("/tmp/claude-0/r1c/relup.py").read())
sys.setrecursionlimit(max(20000, sys.getrecursionlimit()))
PS = os.environ.get("PAIR", "")
NEG = -INF
OBL = []          # (kind, margin, detail)
def obl(kind, m, det): OBL.append((kind, m, det))
def flips(n): return hist[n][1] if n in hist else []
def stable(n, t):
    f = flips(n); i = bisect_right(f, t)
    return (f[i - 1] if i else -10**12), (f[i] if i < len(f) else 10**13)
def pwin(v, u):
    for p in g[v]["pins"]:
        if p["src"] == u and p["live"]: return p["win"][c]
def sep(e1, e2):
    if e1 == e2: return 0
    s, _ = sepAny(e1, e2); return s
def latest(cands):     # among event ids, the one latest in tm
    return max(cands, key=lambda e: tm[e])
ARTFIX = os.environ.get('ARTFIX', '0') == '1'
ARTFIX2 = os.environ.get('ARTFIX2', '0') == '1'; AFTER = []
UNIONREL = os.environ.get('UNIONREL', '0') == '1'; RELU = set(); TRUNC = []
HOLDX = int(os.environ.get('HOLDX', '20000'))
ANCHOR = os.environ.get('ANCHOR', '1') == '1'
COMBREL = os.environ.get('COMBREL', '1') == '1'; COMBTRUNC = os.environ.get('COMBTRUNC', '1') == '1'     # r1c: U' D claims re-anchored at the D input's own last change
SEPNEED = {}; OBLTRIAL = []; ANCLOG = []
def sneed(e1, e2, dneed):      # an accepted obligation uses Sep(e1 -> e2) >= dneed at the current depth
    k = (e1, e2, CURD[0])
    if SEPNEED.get(k, -INF) < dneed: SEPNEED[k] = dneed
MEETN = int(os.environ.get('MEETN', '25'))
GTOP = None
MEETN = int(os.environ.get('MEETN', '25'))
COVL = {}
PEND = []; INSTACK = []; DEPSMAP = {}; OWNBAD = {}; PREV = {}; PEND_PREV = []
memo = {}; inprog = set(); stats = collections.Counter(); DEPS = []; CTX = []
def exwin(u, t):
    k = sum(1 for x in ev[u] if x <= t)
    return dict(A=eid[(u, k - 1)] if k else None, a=0, B=eid[(u, k)] if k < len(ev[u]) else None, b=0, val=valat(u, t), kind="ex")
JOIN = os.environ.get('JOIN', '1') == '1'; JOINN = int(os.environ.get('JOINN', '8')); JOINL = int(os.environ.get('JOINL', '4000'))
_joinmemo = {}
def join_pool(As):
    """the earliest events (topological order) causally after every pin start event: candidate claim starts A with a
    Sep from each pin start (CovTime start); used only when no pin start itself has a Sep from all the others"""
    key = tuple(sorted(set(As)))
    if key in _joinmemo: return _joinmemo[key]
    p0 = max(int(tm[x]) for x in key) + 1
    idx = ord_arr[p0:p0 + JOINL]
    m = np.ones(len(idx), dtype=bool)
    for x in key: m &= VCP[idx, enode[x]] > ek[x]
    r = set(int(e_) for e_ in idx[m][:JOINN]); _joinmemo[key] = r
    if r: stats["claim start via a common causal descendant of the pin starts (JOIN pool non-empty)"] += 1
    return r
def window(pins_w, z):
    """choose (A, a) and (B, b) for a claim of z from its covered pins' windows [(u, w)] (CovTime)"""
    As = [w["A"] for u, w in pins_w if w["A"] is not None]
    if any(w["A"] is None for u, w in pins_w) and not As: A = None; a = 0
    elif not As: A = None; a = 0
    else:
        best = None
        for pool in (set(As), "JOIN"):     # pin events first; then the earliest common causal descendants + consumer anchors
            if pool == "JOIN": pool = (join_pool(As) if JOIN else set()) | set(x_ for x_ in (CTX[-1] if CTX else ()) if x_ != 'noanc')
            for cand in pool:
                reqs = []; ok = True
                for u, w in pins_w:
                    if w["A"] is None: continue
                    d = sep(w["A"], cand)
                    if d == NEG: ok = False; break
                    reqs.append(pwin(z, u)[1] + w["a"] - d)
                if ok:
                    aa = max([0] + reqs)
                    if best is None or et[cand] + aa < et[best[0]] + best[1]: best = (cand, aa)
            if best is not None: break
        if best is None:
            obl("CovTime start (no Sep between pin windows)", NEG, nm[z]); A = latest(As); a = 0
        else:
            A, a = best
            for u, w in pins_w:
                if w["A"] is not None: sneed(w["A"], A, pwin(z, u)[1] + w["a"] - a)
    Bs = [w["B"] for u, w in pins_w if w["B"] is not None]
    if not Bs: B = None; b = 0
    else:
        best = None
        def meet_pool():
            m = VCP[Bs[0]].copy()
            for e_ in Bs[1:]: m = np.minimum(m, VCP[e_])
            cs = [eid[(xs[x], int(m[x]) - 1)] for x in np.nonzero(m)[0]]
            cs.sort(key=lambda e_: -tm[e_])
            if AFTER and AFTER[-1] is not None:      # latch phase: ends causally after the next phase's start first
                ca = [e_ for e_ in cs if leqP(AFTER[-1], e_)]
                if ca: return set(ca[:MEETN])
            if ARTFIX and GTOP is not None and GTOP[0] is not None:     # under a guard: ends causally after E first
                ca = [e_ for e_ in cs if leqP(GTOP[0], e_)]
                if ca: return set(ca[:MEETN])
            return set(cs[:MEETN])
        _ctx = set(x_ for x_ in (CTX[-1] if CTX else ()) if x_ != "noanc")
        pools = ((set(Bs) | _ctx, "MEET") if (GTOP and len(INSTACK) == 1) else (set(Bs), _ctx, "MEET"))
        for pool in pools:
            if isinstance(pool, str):
                if best is not None and not (isinstance(best[2], tuple) and not best[2][0]): break
                pool = meet_pool(); stats["claim end via a common causal ancestor of the pins' end events (tried)"] += 1
            for cand in pool:
                reqs = []; ok = True
                for u, w in pins_w:
                    if w["B"] is None: continue
                    d = sep(cand, w["B"])
                    if d == NEG: ok = False; break
                    reqs.append(pwin(z, u)[0] + w["b"] + d)
                if ok:
                    bb = min(reqs)
                    if bb < 0: continue
                    if GTOP and len(INSTACK) == 1:      # top claim of a guard: pick the end that maximises GuardTime's end margin
                        Eg, lz, hE = GTOP
                        dg = sep(Eg, cand)
                        sc = (dg + lz + bb - hE) if dg != NEG else NEG
                        if best is None or sc > best[2]: best = (cand, bb, sc)
                    elif AFTER and AFTER[-1] is not None:
                        sc = (bool(leqP(AFTER[-1], cand)), et[cand] + bb)
                        if best is None or sc > best[2]: best = (cand, bb, sc)
                    elif ARTFIX and GTOP is not None and GTOP[0] is not None:
                        sc = (bool(leqP(GTOP[0], cand)), et[cand] + bb)
                        if best is None or sc > best[2]: best = (cand, bb, sc)
                    elif best is None or et[cand] + bb > et[best[0]] + best[1]: best = (cand, bb, 0)
            if best is not None and not (isinstance(best[2], tuple) and not best[2][0]): break
        if best is None:
            obl("CovTime end (no Sep between pin windows)", NEG, (nm[z], tuple(Bs), tuple(_ctx))); B = min(Bs, key=lambda e: tm[e]); b = 0
        else:
            B, b = best[0], best[1]
            if b < 0: obl("claim end before its B (b < 0)", b, nm[z]); b = 0
            for u, w in pins_w:
                if w["B"] is not None: sneed(B, w["B"], b - pwin(z, u)[0] - w["b"])
    return A, a, B, b
def lutv(z, assign):     # assign: pin index -> bool or None (X); returns set of outputs
    G = g[z]; xs_ = [j for j in range(G["k"]) if assign.get(j) is None]
    outs = set()
    for bits in itertools.product([False, True], repeat=len(xs_)):
        full = [assign.get(j) for j in range(G["k"])]
        for j, bv in zip(xs_, bits): full[j] = bv
        outs.add(bool(lut(G["init"], G["k"], full)))
        if len(outs) == 2: break
    return outs
def claim(n, t, t2=None):
    """claim for node n's value over the needed interval [t, t2] (inside one simulated stable interval)"""
    sb, se = stable(n, t)
    if t2 is None or t2 < t: t2 = t
    t2 = min(t2, se - 1)
    if n in C["LATCH"]:
        e_ = [g[n]["pins"][p]["src"] for p, v_ in C["LATCH"][n][1] if g[n]["pins"][p]["src"] in EX]
        emd_ = [g[n]["pins"][p]["win"][c][2] for p, v_ in C["LATCH"][n][1] if g[n]["pins"][p]["src"] in EX]
        nk = sum(1 for x in ev[e_[0]] if x + emd_[0] <= t2) if e_ else 0
        key = (n, sb, nk)
    elif n in g and n not in EX and n not in C["const"] and n not in C["data_env"]:
        key = (n, max(t, t0 - 5000), max(t2, t0 - 5000))
    else:
        key = (n, sb)
    key = key + (tuple(sorted(CTX[-1])) if CTX else (),)
    if key in memo:
        if DEPS: DEPS[-1].add(key)
        return memo[key]
    if key in inprog:
        stats["loop cover by an in-progress claim (CovTime checked after the fact)"] += 1
        if DEPS: DEPS[-1].add(key)
        if key in PREV:
            stats["  ...using the previous pass's window of that claim"] += 1
            PEND_PREV.append(key)
            return dict(PREV[key], val=valat(n, t), kind="prev-pass")
        return ("PENDING", key)
    inprog.add(key); INSTACK.append(key)
    val = valat(n, t)
    o0 = len(OBL); DEPS.append(set())
    if n in C["data_env"]:
        cl_ = dict(A=None, a=0, B=None, b=0, val=val, kind="env"); stats["env claims (hEnvC)"] += 1
    elif n in C["const"] or n not in g:
        cl_ = dict(A=None, a=0, B=None, b=0, val=val, kind="const")
    elif n in EX:
        cl_ = exwin(n, t)
    elif n in C["LATCH"]:
        cl_ = latch_claim(n, sb, min(se, t2 + 1), val)
    else:
        cl_ = comb_claim(n, max(t, t0 - 5000), max(t2, t0 - 5000) + 1, val)
    inprog.discard(key); INSTACK.pop()
    deps = DEPS.pop()
    DEPSMAP[key] = set(deps)
    bad_own = [k for k, m, det in OBL[o0:] if m < 0]
    cl_ = dict(cl_) if isinstance(cl_, dict) else cl_
    OWNBAD[key] = bool(bad_own)
    cl_["bad"] = bool(bad_own) or any(memo[d_].get("bad") for d_ in deps if d_ in memo)
    cl_["key"] = key
    memo[key] = cl_
    if DEPS: DEPS[-1].add(key)
    return cl_
def comb_seg(z, s1, s2, val):
    """gate-proved claim of comb z over [s1, s2) (ValOK + CovTime), or None if the stable pins do not decide it"""
    G = g[z]; cand = {}
    tref = max(s1, t0 - 5000)
    for j, p in enumerate(G["pins"]):
        if not p["live"]: continue
        u = p["src"]; lo, hi, md = p["win"][c]
        if u in C["const"] or u not in g and u not in C["data_env"] and u not in EX:
            cand[j] = (u, valat(u, t0), None); continue
        r0, r1 = tref - md, min(s2, 10**12) - md
        usb, use = stable(u, r0)
        if use >= r1: cand[j] = (u, valat(u, r0), r0)
    assign = {j: v_ for j, (u, v_, r) in cand.items()}
    for j, p in enumerate(G["pins"]):
        if not p["live"]: assign[j] = False
    if lutv(z, assign) != {val}: return None
    for j in sorted(cand):          # drop covers greedily
        if cand[j][2] is None: continue
        a2 = dict(assign); a2[j] = None
        if lutv(z, a2) == {val}: assign = a2
    pins_w = []; pend = []
    for j, (u, v_, r) in cand.items():
        if assign.get(j) is None or r is None: continue
        w = claim(u, r, min(s2, 10**12) - G["pins"][j]["win"][c][2])
        if isinstance(w, tuple): pend.append((u, w[1])); continue
        pins_w.append((u, w))
    A, a, B, b = window(pins_w, z)
    for (u, tk) in pend: PEND.append((INSTACK[-1], z, u, tk, (A, a, B, b)))
    return dict(A=A, a=a, B=B, b=b, val=val, kind="comb", cov=[(u, w.get("key")) for u, w in pins_w])
def comb_claim(z, sb, se, val):
    stats["comb claims (GateProof)"] += 1
    r = comb_seg(z, sb, se, val)
    if r is not None: return r
    # split z's stable interval at its pins' (read) change times; one gate-proved claim per segment, chained
    cuts = set()
    lo_t = max(sb, t0 - 5000); hi_t = min(se, 10**12)
    for p in g[z]["pins"]:
        if not p["live"]: continue
        for t in flips(p["src"]):
            tt = t + p["win"][c][2]
            if lo_t < tt < hi_t: cuts.add(tt)
    pts = [lo_t] + sorted(cuts) + [hi_t]
    segs = []
    i = 0
    while i < len(pts) - 1:      # greedy: longest segment from pts[i] that is decided
        jbest = None
        for j in range(len(pts) - 1, i, -1):
            r = comb_seg(z, pts[i], pts[j], val)
            if r is not None: jbest = (j, r); break
        if jbest is None:
            obl("ValOK (output not definite even on a segment between pin changes)", NEG, nm[z]); stats["ValOK fail"] += 1
            return dict(A=None, a=0, B=None, b=0, val=val, kind="fail")
        segs.append(jbest[1]); i = jbest[0]
    stats["comb claims split into a chain"] += 1
    out = [segs[0]]
    for c2 in segs[1:]:
        c1 = out[-1]
        if c1["B"] is None or c2["A"] is None: out.append(c2); continue
        d = sep(c2["A"], c1["B"]); dp = 0
        if COMBREL and (d == NEG or c1["b"] + d - c2["a"] < 0):      # r1c: the relative Up clause for this ChainOK step
            CURD[0] = RELD; d = sep(c2["A"], c1["B"]); CURD[0] = 0; dp = RELD
            if d != NEG and c1["b"] + d - c2["a"] >= 0: RELU.add((c2["A"], c1["B"])); stats["comb segment join passed only with the relative Up"] += 1
        if (d == NEG or c1["b"] + d - c2["a"] < 0) and COMBTRUNC:    # r1c: truncate (ChainOK of the prefix) instead of a failing claim
            stats["comb chain truncated at a failing segment join"] += 1; TRUNC.append((z, "seg", "seg", c2["A"], c1["B"], c1["b"], c2["a"], d)); break
        obl("ChainOK comb segments (next segment starts before the previous ends)", (c1["b"] + d - c2["a"]) if d != NEG else NEG, nm[z])
        if d != NEG and c1["b"] + d - c2["a"] >= 0: CURD[0] = dp; sneed(c2["A"], c1["B"], c2["a"] - c1["b"]); CURD[0] = 0
        out.append(c2)
    return dict(A=out[0]["A"], a=out[0]["a"], B=out[-1]["B"], b=out[-1]["b"], val=val, kind="comb-chain")
def isdcomb(u): return u in g and u not in EX and u not in C["LATCH"] and u not in C["const"] and u not in C["data_env"]
def hmargin(H_, A_, a_):
    """ChainOK H -> U' margin: U'.a <= H.b + Sep(U'.A -> H.B)"""
    if H_["B"] is None or A_ is None: return INF
    d_ = sep(A_, H_["B"])
    return (H_["b"] + d_ - a_) if d_ != NEG else NEG
def reanchor(Q, H_, DwUx, cur):
    """B's anchoring fix: if H -> U' fails, rebuild the U' cover claims of comb D inputs from the D input's own last change
    (an older claim of the same node and value; GateProof/ChainOK as for any comb claim) and keep it if the step passes"""
    m0 = hmargin(H_, cur[0], cur[1])
    if m0 >= 0 or not DwUx: return cur
    stats["U' re-anchor tried (H->U' fails)"] += 1
    for mode in os.environ.get("ANCMODES", "own-last-change").split(","):     # "no-consumer-anchor": opt-in, tested on X25Y76.B5 only
        o1 = len(OBL); dsnap = set(DEPS[-1]); p1 = len(PEND); n1 = dict(SEPNEED)
        pins2 = []; changed = False; ok = True
        for (u, w, ts, te, anc) in DwUx:
            if isdcomb(u):
                sbu = max(stable(u, ts)[0], t0 - 5000)
                if mode == "own-last-change" and sbu < max(ts, t0 - 5000):
                    CTX.append(anc); w2 = claim(u, sbu, te); CTX.pop()
                elif mode == "no-consumer-anchor":      # same D interval, D's start chosen without the latch's open/close anchors
                    CTX.append(("noanc",)); w2 = claim(u, ts, te); CTX.pop()
                else: pins2.append((u, w)); continue
                if isinstance(w2, tuple) or w2.get("bad"): ok = False; break
                pins2.append((u, w2)); changed = True; continue
            pins2.append((u, w))
        if ok and changed:
            A2, a2, B2, b2 = window(pins2, Q)
            m2 = hmargin(H_, A2, a2)
            if m2 >= 0 and len([1 for k_, m_, d_ in OBL[o1:] if m_ < 0]) == 0:
                stats["U' re-anchor accepted (%s)" % mode] += 1; ANCLOG.append((Q, H_["B"], m0, m2, cur[0], A2, mode))
                return (A2, a2, B2, b2)
        stats["U' re-anchor rejected (%s)" % mode] += 1
        OBLTRIAL.extend(OBL[o1:]); del OBL[o1:]; DEPS[-1].clear(); DEPS[-1].update(dsnap); del PEND[p1:]
        SEPNEED.clear(); SEPNEED.update(n1)
    return cur
def latch_claim(Q, sb, se, val):
    fb, en = C["LATCH"][Q]
    enx = [(p, v_) for p, v_ in en if g[Q]["pins"][p]["src"] in EX]
    if len(enx) != 1:
        obl("latch with != 1 exact enable", NEG, nm[Q]); return dict(A=None, a=0, B=None, b=0, val=val, kind="fail")
    pe, act = enx[0]; e = g[Q]["pins"][pe]["src"]; elo, ehi, emd = g[Q]["pins"][pe]["win"][c]
    flo, fhi, fmd = g[Q]["pins"][fb[0]]["win"][c]
    Dp = [j for j, p in enumerate(g[Q]["pins"]) if p["live"] and j not in fb and j != pe and p["src"] not in C["const"]]
    stats["latch claims (ChainOK)"] += 1
    # enable phases (by event index): count n = number of enable events; transparent iff value == act
    def enval(kk): return bool(s0[e]) ^ (kk % 2 == 1)
    kk0 = sum(1 for x in ev[e] if x + emd <= sb)        # enable events read by the time the value appeared
    chain = []
    kk = kk0
    if enval(kk) != bool(act):      # value from a hold phase: only possible before any opening (power-up / t0)
        if kk != 0: obl("latch value appears while closed", NEG, nm[Q])
        chain.append(dict(ph="H", A=None, a=0, B=eid[(e, kk)] if kk < len(ev[e]) else None, b=elo, k=kk))
        stats["hInit (value from before t0)"] += 1
        kk += 1
    while True:
        # transparent phase kk (opened by event kk-1, closes at event kk)
        if kk > len(ev[e]): break
        topen = ev[e][kk - 1] + emd if kk >= 1 else -10**12
        if topen >= se: break
        tclose = ev[e][kk] + emd if kk < len(ev[e]) else 10**13
        tD = max(sb, topen)
        base = {}
        for j, p in enumerate(g[Q]["pins"]):
            if not p["live"]: base[j] = False
            elif p["src"] in C["const"] or (p["src"] not in g and p["src"] not in C["data_env"] and p["src"] not in EX): base[j] = valat(p["src"], t0)
        dval = {j: valat(g[Q]["pins"][j]["src"], tD - g[Q]["pins"][j]["win"][c][2]) for j in Dp}
        def need(env_, fbv):
            asg = dict(base); asg[pe] = env_; asg[fb[0]] = fbv
            asg.update(dval)
            if lutv(Q, asg) != {val}: return None
            keep = set(Dp)
            for j in Dp:
                a2 = dict(asg); a2[j] = None
                if lutv(Q, a2) == {val}: asg = a2; keep.discard(j)
            return keep
        nT = need(bool(act), None); nU = need(None, val)
        hb = dict(base); hb[pe] = not bool(act); hb[fb[0]] = val
        if lutv(Q, hb) != {val}: obl("ValOK latch hold phase", NEG, nm[Q])
        if nT is None: obl("ValOK latch transparent phase", NEG, nm[Q]); nT = set(Dp)
        if nU is None: obl("ValOK latch uncertain phase (D and feedback disagree)", NEG, nm[Q]); nU = set(Dp)
        Dw = []; DwU = []; pendD = []; DwUx = []
        for j in Dp:
            if j not in nT and j not in nU: continue
            u = g[Q]["pins"][j]["src"]; dlo, dhi, dmd = g[Q]["pins"][j]["win"][c]
            anchors = set()
            if kk >= 1: anchors.add(eid[(e, kk - 1)])
            if kk < len(ev[e]): anchors.add(eid[(e, kk)])
            CTX.append(tuple(sorted(anchors)))
            tend_ = min(stable(u, tD - dmd)[1] - 1, max(min(tclose, se), tclose if tclose < 10**12 else se) + HOLDX - dmd)
            w = claim(u, tD - dmd, tend_)
            CTX.pop()
            if not isinstance(w, tuple) and j in nU: DwUx.append((u, w, tD - dmd, tend_, tuple(sorted(anchors))))
            if isinstance(w, tuple): pendD.append((u, w[1], j in nT, j in nU)); continue
            if j in nT: Dw.append((u, w, dlo, dhi)); COVL.setdefault(Q, []).append((u, w.get("key")))
            if j in nU: DwU.append((u, w, dlo, dhi))
        if chain and chain[-1]["ph"] == "H":
            # U' at the re-opening: en X, D covered (the new D), feedback by the union (both agree)
            pinsU = [(u, w) for (u, w, dlo, dhi) in DwU]
            if pinsU:
                AFTER.append(eid[(e, kk - 1)] if (ARTFIX2 and kk >= 1) else None); AU, aU, BU2, bU2 = window(pinsU, Q); AFTER.pop()
                if ANCHOR and not pendD:
                    AU, aU, BU2, bU2 = reanchor(Q, chain[-1], DwUx, (AU, aU, BU2, bU2))
                chain.append(dict(ph="U'", A=AU, a=aU, B=BU2, b=bU2, k=kk))
                for (u, tk, iT, iU) in pendD:
                    if iU: PEND.append((INSTACK[-1], Q, u, tk, (AU, aU, BU2, bU2)))
            else:   # value decided by the feedback alone while the enable read is uncertain: U' = feedback only
                chain.append(dict(ph="U'", A=chain[-1]["A"], a=chain[-1]["a"], B=None, b=0, k=kk))
                stats["re-open covered by feedback alone"] += 1
        # T: en ex(kk) + D covers
        pinsT = [(e, dict(A=eid[(e, kk - 1)] if kk else None, a=0, B=eid[(e, kk)] if kk < len(ev[e]) else None, b=0))]
        pinsT += [(u, w) for (u, w, dlo, dhi) in Dw]
        A, a, B, b = window(pinsT, Q)
        chain.append(dict(ph="T", A=A, a=a, B=B, b=b, k=kk))
        for (u, tk, iT, iU) in pendD:
            if iT: PEND.append((INSTACK[-1], Q, u, tk, (A, a, B, b)))
        if kk >= len(ev[e]) or tclose >= se + 10**12: break
        # U: en X, D covered, fb by the union: starts hi_fb after T's start, ends with D's validity
        pinsU = [(u, w) for (u, w, dlo, dhi) in DwU]
        AFTER.append(eid[(e, kk)] if (ARTFIX2 and kk < len(ev[e])) else None)
        _, _, BU, bU = window(pinsU, Q) if pinsU else (None, 0, None, 0)
        AFTER.pop()
        chain.append(dict(ph="U", A=A, a=a + fhi, B=BU, b=bU, k=kk))
        for (u, tk, iT, iU) in pendD:
            if iU: PEND.append((INSTACK[-1], Q, u, tk, (A, a + fhi, BU, bU)))
        # H: en ex(kk+1) (closed between close event kk and next open kk+1), fb by the union
        Bh = eid[(e, kk + 1)] if kk + 1 < len(ev[e]) else None
        chain.append(dict(ph="H", A=eid[(e, kk)], a=ehi, B=Bh, b=elo, k=kk + 1))
        if Bh is None or ev[e][kk + 1] + emd >= se: break
        kk += 2
    # chain unions; a failing union truncates the claim there (the value is only claimed up to c1's end)
    for i_, (c1, c2) in enumerate(zip(chain, chain[1:])):
        if c1["B"] is None: continue
        if c2["A"] is None: continue
        d = sep(c2["A"], c1["B"])
        if UNIONREL and (d == NEG or c1["b"] + d - c2["a"] < 0):
            CURD[0] = RELD; d = sep(c2["A"], c1["B"]); CURD[0] = 0
            if d != NEG and c1["b"] + d - c2["a"] >= 0: RELU.add((c2["A"], c1["B"])); stats["union passed only with the relative Up"] += 1
        if d == NEG or c1["b"] + d - c2["a"] < 0:
            TRUNC.append((Q, c1["ph"], c2["ph"], c2["A"], c1["B"], c1["b"], c2["a"], d))
            stats["latch claim truncated at a failing union (%s->%s)" % (c1["ph"], c2["ph"])] += 1
            chain = chain[:i_ + 1]; break
        kind = {("T", "U"): "ChainOK T->U (setup: transparent long enough for the feedback)",
                ("U", "H"): "ChainOK U->H (latch hold: D valid past the close read)",
                ("H", "U'"): "ChainOK H->U' (re-latch: new D valid before the re-open read)",
                ("U'", "T"): "ChainOK U'->T (re-latch: transparent phase starts before the new D ends)",
                ("H", "T"): "ChainOK H->T (re-open without D cover)"}.get((c1["ph"], c2["ph"]), "ChainOK")
        obl(kind, (c1["b"] + d - c2["a"]) if d != NEG else NEG, (nm[Q], c1["B"], c2["A"]))
        if (c2["A"], c1["B"]) in RELU: CURD[0] = RELD; sneed(c2["A"], c1["B"], c2["a"] - c1["b"]); CURD[0] = 0
        else: sneed(c2["A"], c1["B"], c2["a"] - c1["b"])
    return dict(A=chain[0]["A"], a=chain[0]["a"], B=chain[-1]["B"], b=chain[-1]["b"], val=val, kind="latch",
                phases=[(ph["ph"], ph["B"]) for ph in chain], cov=COVL.get(Q, []))
# ---------------- guards (window fixpoint: a pass re-uses the previous pass's windows for loop covers)
def mid_(v, w): return dl[(v, w)][2] if (v, w) in dl else 1
NPASS = int(os.environ.get("NPASS", "4"))
NPASS_LAST = [-1]; RELG = []
for pass_ in range(NPASS):
    RELG.clear(); TRUNC.clear(); RELU.clear(); SEPNEED.clear(); OBLTRIAL.clear(); ANCLOG.clear(); memo.clear(); OBL.clear(); stats.clear(); PEND.clear(); DEPSMAP.clear(); OWNBAD.clear(); PEND_PREV.clear()
    G_ = []
    for (v, z), gl in DATAG.items():
        for (st, en_, val) in gl:
            u, j = st; S = eid[(u, j)]; E = eid[en_] if en_ else None
            ts = ev[u][j] + mid_(v, u)
            te_ = (ev[en_[0]][en_[1]] + mid_(v, en_[0])) if en_ else ts
            CTX.append(tuple(sorted([S] + ([E] if E is not None else []))))
            GTOP = (E, pwin(v, z)[0], hi_(v, u)) if E is not None else None
            cz = claim(z, ts - mid_(v, z), te_ - mid_(v, z))
            GTOP = None
            CTX.pop()
            if isinstance(cz, tuple): G_.append((v, z, NEG, "cycle")); continue
            ms = INF; me = INF
            if cz["A"] is not None:
                d = sep(cz["A"], S)
                ms = (d + lo_(v, u) - pwin(v, z)[1] - cz["a"]) if d != NEG else NEG
            if cz["B"] is not None:
                if E is None: me = NEG
                else:
                    d = sep(E, cz["B"])
                    if REL and (d == NEG or d + pwin(v, z)[0] + cz["b"] - hi_(v, u) < 0):
                        CURD[0] = RELD; d = sep(E, cz["B"]); CURD[0] = 0; RELG.append((v, z, st, en_))
                    me = (d + pwin(v, z)[0] + cz["b"] - hi_(v, u)) if d != NEG else NEG
            G_.append((v, z, ms, me, cz, st, en_))
    NEWW = {k: dict(A=v_["A"], a=v_["a"], B=v_["B"], b=v_["b"]) for k, v_ in memo.items() if isinstance(v_, dict)}
    changed = sum(1 for k in NEWW if PREV.get(k) != NEWW[k])
    nf = sum(1 for x in G_ if len(x) == 7 and min(x[2], x[3]) < 0)
    print("  pass %d: claims %d, windows changed vs previous pass %d, loop covers %d (via previous-pass windows %d), guards failing %d" % (
        pass_, len(NEWW), changed, stats["loop cover by an in-progress claim (CovTime checked after the fact)"], len(PEND_PREV), nf), flush=True)
    if changed == 0: break
    PREV = NEWW
# ---------------- loop covers: CovTime against the (now finished) covering claim; then failure propagation
PWHY = collections.Counter(); PEX = []
pbad = set(); npend = 0; pfail = 0; pmin = INF
for (ck, z, u, tk, (A, a, B, b)) in PEND:
    w = memo.get(tk)
    if not isinstance(w, dict): continue
    npend += 1; lo, hi, md = pwin(z, u); ok = True
    if w["A"] is not None:
        if A is None: m = NEG
        else:
            d = sep(w["A"], A); m = (a + d - hi - w["a"]) if d != NEG else NEG
            if m >= 0: sneed(w["A"], A, hi + w["a"] - a)
        if m < 0: ok = False
        elif m < pmin: pmin = m
    if w["B"] is not None:
        if B is None: m = NEG
        else:
            d = sep(B, w["B"]); m = (lo + w["b"] + d - b) if d != NEG else NEG
            if m >= 0: sneed(B, w["B"], b - lo - w["b"])
        if m < 0: ok = False
        elif m < pmin: pmin = m
    if not ok:
        pfail += 1; pbad.add(ck)
        why = []
        if ck == tk: why.append("same claim")
        elif ck[0] == tk[0]: why.append("same node, other window")
        else: why.append("other node")
        why.append("kind %s->%s" % ("latch" if z in C["LATCH"] else "comb", "latch" if tk[0] in C["LATCH"] else "comb"))
        if w["A"] is not None and (A is None or sep(w["A"], A) == NEG or a + sep(w["A"], A) - hi - w["a"] < 0):
            why.append("start: " + ("consumer A none" if A is None else ("no Sep" if sep(w["A"], A) == NEG else "negative")))
        if w["B"] is not None and (B is None or sep(B, w["B"]) == NEG or lo + w["b"] + sep(B, w["B"]) - b < 0):
            why.append("end: " + ("consumer B none" if B is None else ("no Sep" if sep(B, w["B"]) == NEG else "negative")))
        PWHY[tuple(why)] += 1
        if len(PEX) < 4: PEX.append((nm[z], nm[u], nm[tk[0]], A, a, B, b, w["A"], w["a"], w["B"], w["b"]))
    DEPSMAP.setdefault(ck, set()).add(tk)
print("  loop covers (Cov.cl by an in-progress claim, incl. self): %d checked, %d failed CovTime, smallest margin %s" % (npend, pfail, pmin))
for k_, n_ in PWHY.most_common(10): print("    %5d %s" % (n_, k_))
for x in PEX: print("    ex", x[:3], "consumer A,a,B,b", [(nm[el[x[3]][0]], el[x[3]][1]) if x[3] is not None else None, x[4], (nm[el[x[5]][0]], el[x[5]][1]) if x[5] is not None else None, x[6]], "cover", [(nm[el[x[7]][0]], el[x[7]][1]) if x[7] is not None else None, x[8], (nm[el[x[9]][0]], el[x[9]][1]) if x[9] is not None else None, x[10]])
bad = set(k for k, v_ in OWNBAD.items() if v_) | pbad
rev = collections.defaultdict(set)
for k, ds in DEPSMAP.items():
    for d_ in ds: rev[d_].add(k)
todo = list(bad)
while todo:
    k = todo.pop()
    for p_ in rev[k]:
        if p_ not in bad: bad.add(p_); todo.append(p_)
for k, v_ in memo.items():
    if isinstance(v_, dict): v_["bad"] = k in bad
# ---------------- report
kinds = collections.defaultdict(lambda: [0, 0, INF])
for k, m, det in OBL:
    det = det if isinstance(det, str) else det[0]
    kinds[k][0] += 1
    if m < 0: kinds[k][1] += 1
    if m > NEG: kinds[k][2] = min(kinds[k][2], m)
print("[c=%s%s] claims built %d %s" % (c_, PS, len(memo), dict(stats)))
print("  claim obligations (kind: checked / failed / smallest finite margin):")
for k, (n_, f_, mn) in sorted(kinds.items()): print("    %-75s %6d / %5d / %s" % (k, n_, f_, mn))
gf = [x for x in G_ if len(x) == 7 and min(x[2], x[3]) < 0]
gb = [x for x in G_ if len(x) == 7 and x[4].get("bad")]
print("  guards whose claim depends on a failing claim obligation: %d of %d" % (len(gb), len(G_)))
badc = [k for k, v_ in memo.items() if isinstance(v_, dict) and v_.get("bad")]
print("  claims failing (own or inherited): %d of %d" % (len(badc), len(memo)))
print("  guards %d: GuardTime start failed %d, end failed %d, guards failed %d" % (
    len(G_), sum(1 for x in G_ if len(x) == 7 and x[2] < 0), sum(1 for x in G_ if len(x) == 7 and x[3] < 0), len(gf)))
fin = sorted(min(x[2], x[3]) for x in G_ if len(x) == 7 and min(x[2], x[3]) > NEG)
print("  GuardTime finite margins: smallest %s" % fin[:5])
print("  failed guards by data node:", collections.Counter(nm[x[1]] for x in gf).most_common())
reason = collections.Counter()
for x in gf:
    v, z, ms, me, cz, st, en_ = x
    if ms < 0: reason["start: " + ("no Sep claim.A -> S" if ms == NEG else "negative") + " (claim.A = %s)" % (nm[el[cz["A"]][0]] if cz["A"] is not None else None)] += 1
    if me < 0: reason["end: " + ("no Sep E -> claim.B" if me == NEG else "negative") + " (claim.B = %s)" % (nm[el[cz["B"]][0]] if cz["B"] is not None else None)] += 1
for k, n_ in reason.most_common(12): print("    %4d %s" % (n_, k))
exec(open("/tmp/claude-0/r1c/lchk.py").read())
pickle.dump(dict(OBL=OBL, G=G_, stats=dict(stats), UPT=UPT, SEPT=SEPT, TRUNC=TRUNC, RELU=RELU, ANCLOG=ANCLOG, SEPNEED=SEPNEED, MEMO={k: dict(A=v["A"], a=v["a"], B=v["B"], b=v["b"], kind=v["kind"], bad=v.get("bad"), cov=v.get("cov"), phases=v.get("phases")) for k, v in memo.items() if isinstance(v, dict)}, DEPSMAP=DEPSMAP, OWNBAD=OWNBAD, PWHY=dict(PWHY), LCHK=globals().get("LCHKRES")), open("/tmp/claude-0/r1c/datal_c%s%s%s.pkl" % (c_, PS, os.environ.get("TAG", "")), "wb"))
