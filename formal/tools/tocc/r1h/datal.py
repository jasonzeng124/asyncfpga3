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
src = open("/tmp/claude-0/r1h/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
exec(open("/tmp/claude-0/r1h/relup.py").read())
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
CTXAFTER = os.environ.get('CTXAFTER', '1') == '1'; UPMOVE = os.environ.get('UPMOVE', '1') == '1'
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
AFTERA = []; TAFTER = os.environ.get('TAFTER', '1') == '1'
JOIN = os.environ.get('JOIN', '1') == '1'; JOINN = int(os.environ.get('JOINN', '8')); JOINL = int(os.environ.get('JOINL', '4000'))
_joinmemo = {}
JOINTIME = os.environ.get('JOINTIME', '1') == '1'
et_order = np.argsort(et, kind='stable'); et_sorted_v = et[et_order]
def join_pool(As):
    """the earliest events (topological order) causally after every pin start event: candidate claim starts A with a
    Sep from each pin start (CovTime start); used only when no pin start itself has a Sep from all the others"""
    key = tuple(sorted(set(As)))
    if key in _joinmemo: return _joinmemo[key]
    if JOINTIME:      # r1d: candidates by TIME (earliest common successors), not by topological position
        p0 = int(np.searchsorted(et_sorted_v, max(int(et[x]) for x in key), side="left"))
        idx = et_order[p0:p0 + JOINL]
    else:
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
    _pa = bool(AFTERA and AFTERA[-1] and A is not None)
    if _pa: AFTER.append(A)      # r1d TAFTER: a latch T phase ends causally after its own start (T->U needs Sep(T.A -> T.B))
    try:
        B, b = _window_end(pins_w, z)
    finally:
        if _pa: AFTER.pop()
    return A, a, B, b
def _window_end(pins_w, z):
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
            if _cx is not None:
                ca = [e_ for e_ in cs if leqP(_cx, e_)]
                if ca: return set(ca[:MEETN])
            if ARTFIX and GTOP is not None and GTOP[0] is not None:     # under a guard: ends causally after E first
                ca = [e_ for e_ in cs if leqP(GTOP[0], e_)]
                if ca: return set(ca[:MEETN])
            return set(cs[:MEETN])
        _ctx = set(x_ for x_ in (CTX[-1] if CTX else ()) if x_ != "noanc")
        # r1f CTXAFTER: a claim built as a latch's D cover (consumer anchors = that latch's open/close) prefers an end
        # causally after the latest anchor (the close), as U->H needs Sep(close -> U.B); only the choice among candidates
        # that pass CovTime end changes (sneed records each Sep used), so this is a preference, not a new argument.
        _cx = max(_ctx, key=lambda e_: tm[e_]) if (CTXAFTER and _ctx and not (AFTER and AFTER[-1] is not None) and not (GTOP and len(INSTACK) == 1)) else None
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
                    elif _cx is not None:
                        sc = (bool(leqP(_cx, cand)), et[cand] + bb)
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
    return B, b
def lutv(z, assign):     # assign: pin index -> bool or None (X); returns set of outputs
    G = g[z]; xs_ = [j for j in range(G["k"]) if assign.get(j) is None]
    outs = set()
    for bits in itertools.product([False, True], repeat=len(xs_)):
        full = [assign.get(j) for j in range(G["k"])]
        for j, bv in zip(xs_, bits): full[j] = bv
        outs.add(bool(lut(G["init"], G["k"], full)))
        if len(outs) == 2: break
    return outs
RESTART = os.environ.get('RESTART', '1') == '1'; RSLOG = []; RSDBG = []
HOLDRETRY = os.environ.get('HOLDRETRY', '1') == '1'; HOLDLOG = []
HOLDXS = [int(x) for x in os.environ.get('HOLDXS', '80000,320000,100000000').split(',')]
KEEPTRIAL = os.environ.get('KEEPTRIAL', '1') == '1'     # r1d: a rejected trial keeps the loop covers / Seps of sub-claims it built (they stay in memo)
def latch_restart_time(n, t, sb):
    """r1d: a restart point for a latch claim: t itself if Q is transparent at t (as read), else just before the read of
    the close that ended the last transparent phase (a chain may only start with T: H and U' need the union before them;
    the latest restart gives the D claim the latest start, i.e. the most settled pins)"""
    fb, en = C["LATCH"][n]
    enx = [(p, v_) for p, v_ in en if g[n]["pins"][p]["src"] in EX]
    if len(enx) != 1: return None
    pe, act = enx[0]; e = g[n]["pins"][pe]["src"]; emd = g[n]["pins"][pe]["win"][c][2]
    kk = sum(1 for x in ev[e] if x + emd <= t)
    if (bool(s0[e]) ^ (kk % 2 == 1)) == bool(act): return t, kk
    if kk >= 2: return max(sb, ev[e][kk - 1] + emd - 1), kk - 1     # closed at t: restart just before the last close read
    return None
def claim(n, t, t2=None, _rs=None):
    """claim for node n's value over the needed interval [t, t2] (inside one simulated stable interval)"""
    if _rs is None and RESTART and n in C["LATCH"]:
        r0 = claim(n, t, t2, _rs=False)
        if isinstance(r0, dict) and r0.get("trunc") is not None and not r0.get("bad"):
            te = et[r0["B"]] + r0["b"] if r0["B"] is not None else 10**13
            need_end = min(t2 if (t2 is not None and t2 >= t) else t, stable(n, t)[1] - 1)
            if te < need_end:
                trk = latch_restart_time(n, t, stable(n, t)[0])
                tr = (trk[0], int(r0["trunc"]), trk[1]) if trk is not None else None
                if tr is not None and tr[0] > et[r0["trunc"]]:
                    stats["latch restart tried (truncated claim ends before the needed end)"] += 1
                    o1 = len(OBL); p1 = len(PEND); n1 = dict(SEPNEED)
                    rk = (n, int(r0["trunc"]), tr[2])
                    _opt = OPTLOOP and rk not in OPTBAN
                    if _opt: RSTACK.append((rk, int(r0["trunc"]), len(INSTACK)))
                    try: r1 = claim(n, t, t2, _rs=tr)
                    finally:
                        if _opt: RSTACK.pop()
                    RSDBG.append((n, t, tr, r0, r1, [x for x in OBL[o1:] if x[1] < 0][:3]))
                    ok = isinstance(r1, dict) and not r1.get("bad") and (r1["B"] is None or et[r1["B"]] + r1["b"] > te) \
                         and not any(m_ < 0 for k_, m_, d_ in OBL[o1:])
                    if ok:
                        stats["latch restart accepted"] += 1; RSLOG.append((n, t, tr, r0["trunc"], r1["A"], r1["a"], r1["B"], r1["b"]))
                        if DEPS: DEPS[-1].discard(r0["key"])
                        return r1
                    stats["latch restart rejected"] += 1
                    if DEPS and isinstance(r1, dict): DEPS[-1].discard(r1["key"])
                    OBLTRIAL.extend(OBL[o1:]); del OBL[o1:]     # PEND/SEPNEED kept: sub-claims built here stay in memo and may be reused
        return r0
    sb, se = stable(n, t)
    if t2 is None or t2 < t: t2 = t
    t2 = min(t2, se - 1)
    if n in C["LATCH"]:
        e_ = [g[n]["pins"][p]["src"] for p, v_ in C["LATCH"][n][1] if g[n]["pins"][p]["src"] in EX]
        emd_ = [g[n]["pins"][p]["win"][c][2] for p, v_ in C["LATCH"][n][1] if g[n]["pins"][p]["src"] in EX]
        nk = sum(1 for x in ev[e_[0]] if x + emd_[0] <= t2) if e_ else 0
        key = (n, sb, nk) if not _rs else (n, "R", _rs[1], _rs[2], nk)
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
        if RSTACK and INSTACK.index(key) < RSTACK[-1][2]:
            # r1e OPTLOOP: inside a restart trial, a loop cover that closes the loop through the claims being built
            # outside the trial gets an optimistic window (start at the restart's disturbance event, no end); its CovTime
            # is re-verified against the final window after the fixpoint (PEND), and the restart is banned if that fails
            stats["loop cover inside a restart trial: optimistic window"] += 1
            return dict(A=RSTACK[-1][1], a=0, B=None, b=0, val=valat(n, t), kind="opt", key=key, rk=RSTACK[-1][0])
        if key in PREV:
            stats["  ...using the previous pass's window of that claim"] += 1
            PEND_PREV.append(key)
            return dict(PREV[key], val=valat(n, t), kind="prev-pass", key=key)
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
        cl_ = latch_claim(n, sb if not _rs else _rs[0], min(se, t2 + 1), val, restart=bool(_rs))
        if cl_ is None: cl_ = dict(A=None, a=0, B=None, b=0, val=val, kind="restart-none"); obl("latch restart at a closed phase", NEG, nm[n])
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
DROPORD = os.environ.get('DROPORD', '0') == '1'; DROPMASK = os.environ.get('DROPMASK', '0') == '1'
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
    _order = sorted(cand)
    if DROPORD:     # r1h: drop first the covers whose source changes soonest in the run (a pure cover choice; ValOK re-checked)
        _order = sorted(cand, key=lambda j: (stable(cand[j][0], cand[j][2])[1] if cand[j][2] is not None else 10**14, j))
    elif DROPMASK:  # r1h: drop first the MASKED covers: pins whose source changes (as read) before z's own interval ends while z
        # does not (e.g. a mux select whose inputs agree); other pins keep the old order.  A pure cover choice: ValOK re-checked.
        _zse = stable(z, tref)[1]       # z's own simulated stable interval end (not the requested end s2)
        _order = sorted(cand, key=lambda j: (0 if (cand[j][2] is not None and stable(cand[j][0], cand[j][2])[1] + G["pins"][j]["win"][c][2] < _zse) else 1, j))
        if _order != sorted(cand): stats["comb cover drop order: masked pins first (r1h DROPMASK)"] += 1
    for j in _order:          # drop covers greedily
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
    if PREVCHK:
        for (u, w) in pins_w:
            if w.get("kind") in ("prev-pass", "opt"):
                PEND.append((INSTACK[-1], z, u, w["key"], (A, a, B, b))); stats["prev-pass/opt cover registered for the final CovTime re-check"] += 1
                if w.get("rk") is not None: PENDRK[len(PEND) - 1] = w["rk"]
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
    if len(cur) == 4: cur = cur + (None,)
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
                return (A2, a2, B2, b2, pins2)
        stats["U' re-anchor rejected (%s)" % mode] += 1
        OBLTRIAL.extend(OBL[o1:]); del OBL[o1:]; DEPS[-1].clear(); DEPS[-1].update(dsnap)
        if not KEEPTRIAL: del PEND[p1:]; SEPNEED.clear(); SEPNEED.update(n1)
    return cur
FIXU = os.environ.get('FIXU', '1') == '1'; VERIFY = os.environ.get('VERIFY', '1') == '1'; PREVCHK = os.environ.get('PREVCHK', '1') == '1'
FBCOV = os.environ.get('FBCOV', '1') == '1'; HRFREE = FIXU and os.environ.get('HRFREE', '1') == '1'; FBRAISE = os.environ.get('FBRAISE', '1') == '1'
OPTLOOP = os.environ.get('OPTLOOP', '0') == '1'; OPTBAN = set(); RSTACK = []; PENDRK = {}; OPTOUTER = int(os.environ.get('OPTOUTER', '3'))
def pend_ok(ent):
    """CovTime of a loop cover against the (final) covering claim: (ok, margins)"""
    (ck, z, u, tk, (A, a, B, b)) = ent
    w = memo.get(tk)
    if not isinstance(w, dict): return None
    lo, hi, md = pwin(z, u); ok = True
    if w["A"] is not None:
        if A is None: ok = False
        else:
            d = sep(w["A"], A)
            if d == NEG or a + d - hi - w["a"] < 0: ok = False
    if w["B"] is not None:
        if B is None: ok = False
        else:
            d = sep(B, w["B"])
            if d == NEG or lo + w["b"] + d - b < 0: ok = False
    return ok
def u_start(Q, AT, aT, fhi, covs):
    """r1e: start (A, a) of a latch U phase.  Covers: the feedback by the union claim from T (A = T.A, a = T.a, read
    delay hi_fb) and each D pin covered in U by its claim w (CovTime start: hi + w.a <= U.a + Sep(w.A -> U.A)).
    Prefer U.A = T.A with U.a raised as needed; else the best candidate among the pin starts and their joins."""
    items = ([(AT, aT + fhi)] if AT is not None else []) + [(w["A"], pwin(Q, u)[1] + w["a"]) for (u, w) in covs if w["A"] is not None]
    if not items: return None, 0
    if AT is not None:
        reqs = []
        for (x, base) in items:
            d = sep(x, AT)
            if d == NEG: reqs = None; break
            reqs.append(base - d)
        if reqs is not None:
            aa = max([0] + reqs)
            if aa > aT + fhi: stats["U phase start raised for a D pin covered only in U"] += 1
            for (x, base) in items: sneed(x, AT, base - aa)
            return AT, aa
    As = [x for x, _ in items]; best = None
    for pool in (set(As), "JOIN"):
        if pool == "JOIN": pool = (join_pool(As) if JOIN else set()) | set(x_ for x_ in (CTX[-1] if CTX else ()) if x_ != 'noanc')
        for cand in pool:
            reqs = []; ok = True
            for (x, base) in items:
                d = sep(x, cand)
                if d == NEG: ok = False; break
                reqs.append(base - d)
            if ok:
                aa = max([0] + reqs)
                if best is None or et[cand] + aa < et[best[0]] + best[1]: best = (cand, aa)
        if best is not None: break
    if best is None:
        stats["U phase start: no candidate (left at T.A; verify_chain records the failure)"] += 1; return AT, aT + fhi
    stats["U phase start moved off T.A"] += 1
    for (x, base) in items: sneed(x, best[0], base - best[1])
    return best
def verify_chain(Q, chain, fb, pe):
    """r1e: every phase claim of the (final, possibly truncated) chain is a GateProof: CovTime start and end for each
    covered pin (D pins, the exact enable) and for the feedback pin, covered by the union of chain[j..p] (j < p),
    whose end is the phase's own end (so only the start inequality is non-trivial)."""
    for p_, ph in enumerate(chain):
        if ph["a"] < 0: obl("GateProof 0 <= a (latch phase)", ph["a"], nm[Q])
        for (u, w) in ph.get("cov", ()):
            lo, hi, md = pwin(Q, u)
            if w["A"] is not None:
                if ph["A"] is None: m = NEG
                else:
                    d = sep(w["A"], ph["A"]); m = (ph["a"] + d - hi - w["a"]) if d != NEG else NEG
                    if m >= 0: sneed(w["A"], ph["A"], hi + w["a"] - ph["a"])
                obl("CovTime start, latch phase %s (re-verified)" % ph["ph"], m, (nm[Q], nm[u]))
            if w["B"] is not None:
                if ph["B"] is None: m = NEG
                else:
                    d = sep(ph["B"], w["B"]); m = (lo + w["b"] + d - ph["b"]) if d != NEG else NEG
                    if m >= 0: sneed(ph["B"], w["B"], ph["b"] - lo - w["b"])
                obl("CovTime end, latch phase %s (re-verified)" % ph["ph"], m, (nm[Q], nm[u]))
            if PREVCHK and w.get("kind") in ("prev-pass", "opt"):
                PEND.append((INSTACK[-1], Q, u, w["key"], (ph["A"], ph["a"], ph["B"], ph["b"]))); stats["prev-pass/opt cover registered for the final CovTime re-check"] += 1
                if w.get("rk") is not None: PENDRK[len(PEND) - 1] = w["rk"]
        if FBCOV and ph["ph"] != "T":
            flo, fhi, fmd = g[Q]["pins"][fb[0]]["win"][c]
            best = NEG; bj = None
            for j in range(p_ + 1):
                cj = chain[j]
                if cj["A"] is None: m = INF
                elif ph["A"] is None: continue
                else:
                    d = sep(cj["A"], ph["A"])
                    if d == NEG: continue
                    m = ph["a"] + d - fhi - cj["a"]
                if m > best: best = m; bj = j
            if best >= 0 and chain[bj]["A"] is not None: sneed(chain[bj]["A"], ph["A"], fhi + chain[bj]["a"] - ph["a"])
            obl("CovTime start, latch phase %s feedback by a union chain[j..p] (re-verified)" % ph["ph"], best, (nm[Q], ph["ph"], p_))
def latch_claim(Q, sb, se, val, restart=False):
    global GTOP
    if os.environ.get('LGTOPOFF', '1') == '1' and GTOP is not None:   # B's LGTOPOFF (guard-optimal end not for a latch's internal phases)
        g_ = GTOP; GTOP = None
        try: return latch_claim(Q, sb, se, val, restart)
        finally: GTOP = g_
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
    chain = []; trunc_ev = None
    kk = kk0
    if enval(kk) != bool(act):      # value from a hold phase: only possible before any opening (power-up / t0)
        if restart: return None
        if kk != 0: obl("latch value appears while closed", NEG, nm[Q])
        chain.append(dict(ph="H", A=None, a=0, B=eid[(e, kk)] if kk < len(ev[e]) else None, b=elo, k=kk,
                          cov=[(e, dict(A=eid[(e, kk - 1)] if kk else None, a=0, B=eid[(e, kk)] if kk < len(ev[e]) else None, b=0))]))
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
            if pinsU or any(iU for (u, tk, iT, iU) in pendD):
                AFTER.append(eid[(e, kk - 1)] if (ARTFIX2 and kk >= 1) else None); AU, aU, BU2, bU2 = window(pinsU, Q); AFTER.pop()
                if ANCHOR and not pendD:
                    _ra = reanchor(Q, chain[-1], DwUx, (AU, aU, BU2, bU2, pinsU))
                    AU, aU, BU2, bU2 = _ra[:4]; pinsU = _ra[4]
                chain.append(dict(ph="U'", A=AU, a=aU, B=BU2, b=bU2, k=kk, cov=list(pinsU)))
                for (u, tk, iT, iU) in pendD:
                    if iU: PEND.append((INSTACK[-1], Q, u, tk, (AU, aU, BU2, bU2)))
            else:   # value decided by the feedback alone while the enable read is uncertain: U' = feedback only
                chain.append(dict(ph="U'", A=chain[-1]["A"], a=chain[-1]["a"], B=None, b=0, k=kk, cov=[], fbonly=True))
                stats["re-open covered by feedback alone"] += 1
        # T: en ex(kk) + D covers
        pinsT = [(e, dict(A=eid[(e, kk - 1)] if kk else None, a=0, B=eid[(e, kk)] if kk < len(ev[e]) else None, b=0))]
        pinsT += [(u, w) for (u, w, dlo, dhi) in Dw]
        AFTERA.append(TAFTER); A, a, B, b = window(pinsT, Q); AFTERA.pop()
        chain.append(dict(ph="T", A=A, a=a, B=B, b=b, k=kk, cov=list(pinsT)))
        for (u, tk, iT, iU) in pendD:
            if iT: PEND.append((INSTACK[-1], Q, u, tk, (A, a, B, b)))
        if kk >= len(ev[e]) or tclose >= se + 10**12: break
        # U: en X, D covered, fb by the union: starts hi_fb after T's start, ends with D's validity
        pinsU = [(u, w) for (u, w, dlo, dhi) in DwU]
        AFTER.append(eid[(e, kk)] if (ARTFIX2 and kk < len(ev[e])) else None)
        _, _, BU, bU = window(pinsU, Q) if pinsU else (None, 0, None, 0)
        if HOLDRETRY and pinsU and not pendD and kk < len(ev[e]) and BU is not None:
            # r1d: U->H fails because D's claim ends at an event unordered with (or before) the close: the D claims were
            # only asked for HOLDX past the close.  Ask for them further (still inside D's simulated stable interval), so
            # their end can be an event causally after the close.  Kept only if U->H then passes.
            Hc = eid[(e, kk)]
            def _uh(B_, b_):
                d_ = sep(Hc, B_); return (b_ + d_ - ehi) if d_ != NEG else NEG
            if _uh(BU, bU) < 0:
                stats["U->H hold retry with longer D claims (tried)"] += 1
                for hx in HOLDXS:
                    pins2 = []; okp = True
                    for (u, w, ts_, te_, anc) in DwUx:
                        te2 = min(stable(u, ts_)[1] - 1, tclose + hx - g[Q]["pins"][[jj for jj in Dp if g[Q]["pins"][jj]["src"] == u][0]]["win"][c][2])
                        if te2 <= te_: pins2.append((u, w)); continue
                        CTX.append(anc); w2 = claim(u, ts_, te2); CTX.pop()
                        if isinstance(w2, tuple) or w2.get("bad"): okp = False; break
                        pins2.append((u, w2))
                    if not okp: continue
                    _, _, BU2, bU2 = window(pins2, Q)
                    # U keeps T's start (U.A = T.A, U.a = T.a + hi_fb): CovTime start against each new D claim
                    cst = []
                    for (u, w2) in pins2:
                        if w2["A"] is None: continue
                        if A is None: cst = None; break
                        d_ = sep(w2["A"], A)
                        if d_ == NEG or pwin(Q, u)[1] + w2["a"] > a + fhi + d_: cst = None; break
                        cst.append((w2["A"], pwin(Q, u)[1] + w2["a"] - a - fhi))
                    if cst is None and HRFREE and A is not None and all(sep(w2["A"], A) != NEG for (u, w2) in pins2 if w2["A"] is not None):
                        cst = []; stats["U->H hold retry: U start raised by u_start (T->U re-checked)"] += 1
                    if cst is None: continue
                    if BU2 is None or _uh(BU2, bU2) >= 0:
                        for (x1, dn) in cst: sneed(x1, A, dn)
                        if BU2 is not None: sneed(Hc, BU2, ehi - bU2)
                        stats["U->H hold retry accepted"] += 1; HOLDLOG.append((Q, kk, hx, BU, BU2))
                        BU, bU = BU2, bU2; DwU = [(u, w2, 0, 0) for (u, w2) in pins2]; break
        AFTER.pop()
        AUs, aUs = A, a + fhi
        if FIXU: AUs, aUs = u_start(Q, A, a, fhi, [(u, w) for (u, w, _1, _2) in DwU])
        chain.append(dict(ph="U", A=AUs, a=aUs, B=BU, b=bU, k=kk, cov=[(u, w) for (u, w, _1, _2) in DwU]))
        for (u, tk, iT, iU) in pendD:
            if iU: PEND.append((INSTACK[-1], Q, u, tk, (AUs, aUs, BU, bU)))
        # H: en ex(kk+1) (closed between close event kk and next open kk+1), fb by the union
        Bh = eid[(e, kk + 1)] if kk + 1 < len(ev[e]) else None
        chain.append(dict(ph="H", A=eid[(e, kk)], a=ehi, B=Bh, b=elo, k=kk + 1, cov=[(e, dict(A=eid[(e, kk)], a=0, B=Bh, b=0))]))
        if Bh is None or ev[e][kk + 1] + emd >= se: break
        kk += 2
    if FIXU:      # r1e: a U' decided by the feedback alone ends with the next phase (its feedback cover ends there too)
        for i_, ph in enumerate(chain):
            if ph.get("fbonly") and i_ + 1 < len(chain): ph["B"] = chain[i_ + 1]["B"]; ph["b"] = chain[i_ + 1]["b"]
    if FBRAISE:   # r1e: raise a non-T phase's offset a so its feedback cover (union chain[j..p]) meets CovTime start
        _flo, _fhi, _ = g[Q]["pins"][fb[0]]["win"][c]
        for p_, ph in enumerate(chain):
            if ph["ph"] == "T" or ph["A"] is None: continue
            need = None
            for j in range(p_):
                cj = chain[j]
                if cj["A"] is None: need = -INF; break
                d = sep(cj["A"], ph["A"])
                if d == NEG: continue
                r_ = _fhi + cj["a"] - d
                if need is None or r_ < need: need = r_
            if need is None and UPMOVE and ph["ph"] == "U'" and p_ >= 1 and chain[p_ - 1]["ph"] == "H" and chain[p_ - 1]["A"] is not None:
                # r1f UPMOVE: U' starts (at its D covers' start) before every earlier phase, so no union chain[j..p] covers
                # its feedback.  Move U'.A to the preceding H's start (the close); a covers fhi after H and every D cover's
                # CovTime start (needs Sep(D.A -> H.A)).  verify_chain re-checks all of it; H->U' ChainOK is checked below.
                Hp = chain[p_ - 1]; A2 = Hp["A"]; reqs = [_fhi + Hp["a"]]; okm = True
                for (u, w) in ph["cov"]:
                    if w.get("A") is None: continue
                    d = sep(w["A"], A2)
                    if d == NEG: okm = False; break
                    reqs.append(pwin(Q, u)[1] + w["a"] - d)
                if okm:
                    stats["U' start moved to the preceding close (feedback cover)"] += 1
                    ph["A"] = A2; ph["a"] = max(reqs); continue
            if need is not None and need > ph["a"]:
                stats["latch phase offset raised for its feedback cover (%s)" % ph["ph"]] += 1; ph["a"] = need
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
            chain = chain[:i_ + 1]; trunc_ev = c1["B"]; break
        kind = {("T", "U"): "ChainOK T->U (setup: transparent long enough for the feedback)",
                ("U", "H"): "ChainOK U->H (latch hold: D valid past the close read)",
                ("H", "U'"): "ChainOK H->U' (re-latch: new D valid before the re-open read)",
                ("U'", "T"): "ChainOK U'->T (re-latch: transparent phase starts before the new D ends)",
                ("H", "T"): "ChainOK H->T (re-open without D cover)"}.get((c1["ph"], c2["ph"]), "ChainOK")
        obl(kind, (c1["b"] + d - c2["a"]) if d != NEG else NEG, (nm[Q], c1["B"], c2["A"]))
        if (c2["A"], c1["B"]) in RELU: CURD[0] = RELD; sneed(c2["A"], c1["B"], c2["a"] - c1["b"]); CURD[0] = 0
        else: sneed(c2["A"], c1["B"], c2["a"] - c1["b"])
    if VERIFY: verify_chain(Q, chain, fb, pe)
    return dict(A=chain[0]["A"], a=chain[0]["a"], B=chain[-1]["B"], b=chain[-1]["b"], val=val, kind="latch",
                phases=[(ph["ph"], ph["B"]) for ph in chain], cov=COVL.get(Q, []), trunc=trunc_ev, restart=restart)
# ---------------- guards (window fixpoint: a pass re-uses the previous pass's windows for loop covers)
def mid_(v, w): return dl[(v, w)][2] if (v, w) in dl else 1
NPASS = int(os.environ.get("NPASS", "4"))
NPASS_LAST = [-1]; RELG = []
import time as _tpass; _T0 = _tpass.time()
for outer_ in range(OPTOUTER if OPTLOOP else 1):
  PREV = {}
  for pass_ in range(NPASS):
      PENDRK.clear(); RELG.clear(); RSLOG.clear(); HOLDLOG.clear(); RSDBG.clear(); TRUNC.clear(); RELU.clear(); SEPNEED.clear(); OBLTRIAL.clear(); ANCLOG.clear(); memo.clear(); OBL.clear(); stats.clear(); PEND.clear(); DEPSMAP.clear(); OWNBAD.clear(); PEND_PREV.clear()
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
      print("  pass %d: claims %d, windows changed vs previous pass %d, loop covers %d (via previous-pass windows %d), guards failing %d, %.0fs" % (
          pass_, len(NEWW), changed, stats["loop cover by an in-progress claim (CovTime checked after the fact)"], len(PEND_PREV), nf, _tpass.time() - _T0), flush=True)
      CONVERGED = changed == 0
      if changed == 0: break
      PREV = NEWW
  if not OPTLOOP: break
  _fail_rk = set(PENDRK[i_] for i_, ent in enumerate(PEND) if i_ in PENDRK and pend_ok(ent) is False)
  _used_rk = set(PENDRK.values())
  print("  outer %d: optimistic loop covers %d (restarts using them %d); failing their final CovTime %d -> restarts banned %d" % (
      outer_, len(PENDRK), len(_used_rk), sum(1 for i_, ent in enumerate(PEND) if i_ in PENDRK and pend_ok(ent) is False), len(_fail_rk - OPTBAN)), flush=True)
  if not (_fail_rk - OPTBAN): break
  OPTBAN |= _fail_rk
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
print("  fixpoint converged: %s" % CONVERGED)
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
exec(open("/tmp/claude-0/r1h/lchk.py").read())
pickle.dump(dict(OBL=OBL, G=G_, stats=dict(stats), UPT=UPT, SEPT=SEPT, TRUNC=TRUNC, RELU=RELU, ANCLOG=ANCLOG, RSLOG=RSLOG, HOLDLOG=HOLDLOG, SEPNEED=SEPNEED, MEMO={k: dict(A=v["A"], a=v["a"], B=v["B"], b=v["b"], kind=v["kind"], bad=v.get("bad"), cov=v.get("cov"), phases=v.get("phases"), trunc=v.get("trunc"), restart=v.get("restart")) for k, v in memo.items() if isinstance(v, dict)}, DEPSMAP=DEPSMAP, OWNBAD=OWNBAD, PWHY=dict(PWHY), LCHK=globals().get("LCHKRES")), open("/tmp/claude-0/r1h/datal_c%s%s%s.pkl" % (c_, PS, os.environ.get("TAG", "")), "wb"))
