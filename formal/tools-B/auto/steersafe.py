#!/usr/bin/env python3
"""tools-B/auto/steersafe.py MDIR STEER COND LAUNCH  (shard B, 2026-11-20; UNTRUSTED extraction + arithmetic; logic = Lean
SteerSettle.steer_reads_settled / steer_out_forced (the two windows -> the steer reads the settled condition),
SettleAll.settle_all for the condition side (ForceTree.force_tree with a pin SUBSET for an opened link latch: the pins
its INIT depends on while its enable is 1, tied pins at their constants; the enable source is a root showing 1 from A), ChainHold.chain_hold (v = 0) and CtlChain.hold_mem (a C-element that is 0
and has a pin at 0 stays 0) for the request side): a lower bound (kappa_lo) for the STEER SETTLE race of a decoded route
-- research's rule E: a steer's condition must have settled at the steer LUT before the steer's request reaches it.

Problem, plainly. A branch steer bd_steer is a LUT reading a request (from its join, `<steer>_j`) and a condition (a
compare's result). If the condition is still moving when the request arrives, the steer can send the token the wrong
way. Research's post-route trims (research/data/trim/README.md) shorten the compare's matched delay, which is what keeps
the request behind the condition. This bounds the race for EVERY delay in the band at a given kappa (g = 1).

STEER: regex for the steer's LUT cells (e.g. 'ucond_br5\\.u\\$LUT6'); COND: regex for the condition's driving cell
(e.g. 'ucmpi0\\.uz_n3$'); LAUNCH: regex for the storage cell whose rise A launches both sides (the compare's join,
e.g. 'ucmpi0\\.ujoin').
Request side: from the steer pin whose source is a join, walk back through gates; a pin counts if it ALONE forces its
gate to 0 (chain_hold's premise, decided on the INIT with constant-tied pins at their values), or, for a storage gate
(reads its own output), if it forces 0 together with the feedback pin at 0 (hold_mem: a PREMISE that the storage node
is 0 when the walk reaches it, i.e. the four-phase return to zero has happened before A; listed). R = the largest sum of
minimum composite pin delays over such paths from LAUNCH (any path is a valid bound).
Condition side: the backward cone of the condition pin, stopped at storage LUTs / boundary nodes, acyclic; D = longest
path of maximum delays, every root counted as settled at A (PREMISE: the compare's operand latches hold from before A
to the capture; listed with the roots' cells).
kappa_lo = min over corners c in {0, 1} of (R - D) / (R + D), with both sides' pin arcs into the steer LUT included."""
import json, re, sys, collections
AUTO = "--auto" in sys.argv
M, STEER, COND, LAUNCH = (sys.argv[1], r"ucond_br\d+\.u\$LUT[56]", None, None) if AUTO else sys.argv[1:5]; CLS = sys.argv[sys.argv.index("--classes") + 1] if "--classes" in sys.argv else None
N = json.load(open(M + "/net.json")); G = N["gates"]; names = N["nodes"]
BB = json.load(open(M + "/bnd.json")); idx = {n: i for i, n in enumerate(names)}
env = {idx[v] if isinstance(v, str) else v for v in BB["env"]}
cells = json.load(open(M + "/routed.json"))["modules"]["top"]["cells"]
bel = {v["attributes"].get("NEXTPNR_BEL"): k for k, v in cells.items()}
drv = {g["out"]: gi for gi, g in enumerate(G)}
def cellof(g):
    m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", g["name"])
    return bel.get("%s/%s%sLUT" % m.groups(), "") if m else g["name"]
def through(u):
    for _ in range(400):
        gi = drv.get(u)
        if gi is None or G[gi]["kind"] not in ("pip", "hop"): return u
        u = G[gi]["ins"][0]
    return u
def ncell(u): gi = drv.get(u); return cellof(G[gi]) if gi is not None else names[u]
storage = {g["out"] for g in G if g["kind"] in ("lut5", "lut6") and any(through(u) == g["out"] for u in g["ins"])}
lerp = lambda a, b, c: a + (b - a) * c
sys.setrecursionlimit(1000000)
def constval(u):
    s = through(u); gi = drv.get(s)
    if gi is None or G[gi]["kind"] != "const": return None
    return 1 if "VCC" in G[gi]["name"].upper() else 0 if "GND" in G[gi]["name"].upper() else None
def forces0(g, q, fbpins=()):
    """pin q at 0 (and every pin in fbpins at 0) forces g to 0, constant-tied pins at their values."""
    k = len(g["ins"]); init = int(g["init"]); fix = {i: constval(u) for i, u in enumerate(g["ins"])}
    def ok(ad):
        if (ad >> q) & 1: return False
        if any((ad >> f) & 1 for f in fbpins): return False
        return all(v is None or ((ad >> i) & 1) == v for i, v in fix.items())
    return all(not ((init >> ad) & 1) for ad in range(1 << k) if ok(ad))
steer = [(gi, g) for gi, g in enumerate(G) if g["kind"] in ("lut5", "lut6") and re.search(STEER, cellof(g))]
launch = set() if AUTO else {g["out"] for g in G if g["kind"] in ("lut5", "lut6") and g["out"] in storage and re.search(LAUNCH, cellof(g))}
if not AUTO and (not steer or not launch): sys.exit("steer %d gates, launch %d storage nodes: nothing to do" % (len(steer), len(launch)))
PREM = set()
WALK = set()
def req_bound(u0, c):
    memo, onst = {}, set()
    def R(u):   # -> best (largest) sum of min delays from a LAUNCH node to u, or None
        if u in launch: return 0.0
        if u in memo: return memo[u]
        gi = drv.get(u)
        if gi is None or u in env or u in onst: return None
        onst.add(u); g = G[gi]; best = None
        fb = [i for i, w in enumerate(g["ins"]) if g["kind"] in ("lut5", "lut6") and through(w) == u]
        for q in range(len(g["ins"])):
            if q in fb or constval(g["ins"][q]) is not None: continue
            if not (g["kind"] in ("pip", "hop") or forces0(g, q, fb)): continue
            r = R(g["ins"][q])
            if r is None: continue
            if fb: PREM.add("storage %s is 0 at A (hold_mem)" % cellof(g).replace("bridge_i.udut.", ""))
            t = r + lerp(g["arcs"][q]["fmin"], g["arcs"][q]["smin"], c)
            if best is None or t > best: best = t
        onst.discard(u); memo[u] = best
        if best is not None: WALK.add(u)
        return best
    return R(u0)
FBM = {}
def fbpins(u):
    """pins left out when u is expanded as an open latch: its own feedback, and every pin the INIT does not depend on
    while the enable (the pin read from a '.ctl.' node) is 1, tied pins at their constants (a LUT6_2 pair latch reads
    its sibling half, which O6 ignores)."""
    if u in FBM: return FBM[u]
    gi = drv.get(u); g = G[gi]
    fb = {i for i, w in enumerate(g["ins"]) if g["kind"] in ("lut5", "lut6") and through(w) == u}
    en = [i for i, w in enumerate(g["ins"]) if re.search(r"\.ctl\.", ncell(through(w)))]
    if g["kind"] in ("lut5", "lut6") and len(en) == 1:
        k = len(g["ins"]); init = int(g["init"]); fix = {i: constval(w) for i, w in enumerate(g["ins"])}
        ok = lambda ad: ((ad >> en[0]) & 1) == 1 and all(v is None or ((ad >> i) & 1) == v for i, v in fix.items())
        for i in range(k):
            if i == en[0] or fix[i] is not None: continue
            if all(((init >> ad) & 1) == ((init >> (ad ^ (1 << i))) & 1) for ad in range(1 << k) if ok(ad)): fb.add(i)
    FBM[u] = fb; return fb
CUT = set()   # launch nodes: an opened latch's pins NOT read from one of these are roots (settled at A: the link's bundling)
CUTONLY = None   # if a set: the CUT rule applies to these opened latches only (others are expanded through every pin)
def cone(u0, opened=frozenset()):
    """backward cone of u0 stopped at storage / env (roots), except storage nodes in `opened`, which are expanded
    with their feedback pins left out (a latch whose output is the condition)."""
    isl, roots, st = set(), set(), [u0]
    while st:
        u = st.pop()
        if u in isl or u in roots: continue
        gi = drv.get(u)
        if gi is None or (u in storage and u not in opened) or u in env: roots.add(u); continue
        isl.add(u); fb = fbpins(u) if u in opened else set()
        for i, w in enumerate(G[gi]["ins"]):
            if i in fb: continue
            if u in opened and CUT and (CUTONLY is None or u in CUTONLY) and through(w) not in CUT: roots.add(w); continue
            st.append(w)
    order, state = [], {}
    def visit(u):
        if u in roots: return True
        s = state.get(u)
        if s == 1: return False
        if s == 2: return True
        state[u] = 1
        fb = fbpins(u) if u in opened else set()
        for i, v in enumerate(G[drv[u]]["ins"]):
            if i in fb: continue
            if u in opened and CUT and (CUTONLY is None or u in CUTONLY) and through(v) not in CUT: continue
            if not visit(v): return False
        state[u] = 2; order.append(u); return True
    return isl, roots, order, visit(u0)
def data_bound(u0, order, roots, c, opened=frozenset()):
    t = {}
    for u in order:
        g = G[drv[u]]; fb = fbpins(u) if u in opened else set()
        t[u] = max(((0 if v in roots else t[v]) + lerp(g["arcs"][p]["fmax"], g["arcs"][p]["smax"], c) for p, v in enumerate(g["ins"]) if p not in fb), default=0)
    return 0 if u0 in roots else t[u0]
EXPLAIN = "--explain" in sys.argv   # 2026-11-21: print both paths of each term hop by hop (cells vs routing), with --only
def _hop(gg, i, c, mx):
    a = gg["arcs"][i]; d = lerp(a["fmax"], a["smax"], c) if mx else lerp(a["fmin"], a["smin"], c)
    return d, ("route" if gg["kind"] in ("pip", "hop") else "cell")
def explain(g, p, q, c, t, order, roots, rset, opened):
    """the condition's longest path (max arcs) and the request's forcing walk (min arcs) behind one term, corner c."""
    # condition: follow the argmax input back from the steer's condition pin
    hops, u = [], g["ins"][q]; d0, k0 = _hop(g, q, c, True); hops.append((cellof(g), k0, d0))
    while u not in roots and u in t:
        gg = G[drv[u]]; fb = fbpins(u) if u in opened else set(); best = None
        for i, v in enumerate(gg["ins"]):
            if i in fb: continue
            x = (0 if v in rset else None) if v in roots else t.get(v)
            if x is None: continue
            d, kd = _hop(gg, i, c, True)
            if best is None or x + d > best[0]: best = (x + d, v, d, kd)
        if best is None: break
        hops.append((cellof(gg), best[3], best[2])); u = best[1]
    cs_ = sum(h[2] for h in hops if h[1] == "cell"); rt_ = sum(h[2] for h in hops if h[1] == "route")
    print("  EXPLAIN corner %d condition path from %s: %d hops, cells %.0f ps + routing %.0f ps = %.0f ps" % (c, ncell(u).replace("bridge_i.udut.", ""), len(hops), cs_, rt_, cs_ + rt_))
    for h in reversed(hops):
        if h[1] == "cell": print("    cond  %-60s %6.0f ps" % (h[0].replace("bridge_i.udut.", ""), h[2]))
    # request: re-walk the forcing paths (min arcs), largest sum
    memo = {}
    def RR(u, seen):
        if u in launch: return (0.0, [])
        if u in memo: return memo[u]
        gi = drv.get(u)
        if gi is None or u in env or u in seen: return None
        gg = G[gi]; best = None; seen = seen | {u}
        fb = [i for i, w in enumerate(gg["ins"]) if gg["kind"] in ("lut5", "lut6") and through(w) == u]
        for i in range(len(gg["ins"])):
            if i in fb or constval(gg["ins"][i]) is not None: continue
            if not (gg["kind"] in ("pip", "hop") or forces0(gg, i, fb)): continue
            r = RR(gg["ins"][i], seen)
            if r is None: continue
            d, kd = _hop(gg, i, c, False)
            if best is None or r[0] + d > best[0]: best = (r[0] + d, r[1] + [(cellof(gg), kd, d)])
        memo[u] = best; return best
    r = RR(g["ins"][p], frozenset())
    if r:
        d0, k0 = _hop(g, p, c, False); hp = r[1] + [(cellof(g), k0, d0)]
        cs_ = sum(h[2] for h in hp if h[1] == "cell"); rt_ = sum(h[2] for h in hp if h[1] == "route")
        print("  EXPLAIN corner %d request walk: %d hops, cells %.0f ps + routing %.0f ps = %.0f ps" % (c, len(hp), cs_, rt_, cs_ + rt_))
        for h in hp:
            if h[1] == "cell": print("    req   %-60s %6.0f ps" % (h[0].replace("bridge_i.udut.", ""), h[2]))
def auto():
    """every steer of the route: condition from a compare's output (launch = its .ujoin) or from a link latch (launch =
    that stage's .ctl, the latch expanded in the condition cone without its feedback pin)."""
    global launch, CUTONLY
    rows = []
    for gi, g in enumerate(G):
        ismux = MUX and bool(re.search(r"\.uj\d+$", cellof(g)))
        if g["kind"] not in ("lut5", "lut6") or not (re.search(STEER, cellof(g)) or ismux): continue
        if ONLY and not re.search(ONLY, cellof(g)): continue
        CUT.clear()
        src = [through(u) for u in g["ins"]]
        if ismux:   # a mux join (C-element) reading its select link's latch and that link's request line
            fbm = {i for i, w in enumerate(g["ins"]) if through(w) == g["out"]}
            cp = [p for p, s in enumerate(src) if p not in fbm and re.search(r"\.lat\.", ncell(s)) and s in storage]
            if len(cp) != 1: rows.append((None, cellof(g).replace("bridge_i.udut.", ""), "mux join: select latch pins %s: skipped" % cp)); continue
            lk = re.sub(r"\.lat\..*$", "", ncell(src[cp[0]]))
            rp = [p for p, s in enumerate(src) if ncell(s).startswith(lk + ".rdly.") or ncell(s).startswith(lk + ".ctl.")]
        else:
            rp = [p for p, s in enumerate(src) if re.search(r"_j\.", ncell(s))]
            cp = [p for p, s in enumerate(src) if p not in rp and constval(g["ins"][p]) is None and drv.get(s) is not None]
        name = cellof(g).replace("bridge_i.udut.", "")
        if len(rp) != 1 or len(cp) != 1: rows.append((None, name, "request pins %s condition pins %s: skipped" % (rp, cp))); continue
        p, q = rp[0], cp[0]; cs = src[q]; cc = ncell(cs)
        m1 = re.match(r"^(.*)\.uz_n\d+$", cc); m2 = re.match(r"^(.*)\.lat\.[a-z]+(\[\d+\])?\.u(\$LUT[56])?$", cc)
        if m1: lre, opened, kind = re.escape(m1.group(1)) + r"\.ujoin", frozenset(), "compare"
        elif m2 and cs in storage: lre, opened, kind = None, frozenset([cs]), "latch"
        else: rows.append((None, name, "condition from %s: kind not handled" % cc)); continue
        isl, roots, order, acyc = cone(g["ins"][q], opened)
        if not acyc: rows.append((None, name, "condition cone cyclic")); continue
        if lre is None:   # a transparent link latch holds the condition: launch = the join of the compute that feeds it
            own = m2.group(1).replace("bridge_i.udut.", "")
            inst = sorted({mm.group(1) for u in isl for mm in [re.match(r"^bridge_i\.udut\.([A-Za-z0-9_]+)\.", ncell(u))] if mm
                           and not mm.group(1).startswith("ulink")} - {own})
            lre = (r"bridge_i\.udut\.(%s)\.ujoin" % "|".join(re.escape(i) for i in inst)) if inst else "(no compute: ctl only)"
        launch = {G[j]["out"] for j in range(len(G)) if G[j]["kind"] in ("lut5", "lut6") and G[j]["out"] in storage and re.search(lre, cellof(G[j]))}
        if not launch and kind == "compare":   # a one-channel compare has no join: its line starts at the input link's ctl
            inst = m1.group(1)
            uor = [G[j] for j in range(len(G)) if G[j]["kind"] in ("lut5", "lut6") and cellof(G[j]) == inst + ".uor"]
            launch = {through(w) for gg in uor for w in gg["ins"] if constval(w) is None and through(w) in storage}
            if launch:   # the operand latches of that link open on the same rise: expand them (feedback pins left out;
                # their data pins are roots settled at A, a premise: the input link's own bundling)
                CUT.clear(); CUT.update(launch)
                lre = "|".join(sorted(ncell(u) for u in launch)) + " (joinless compare: the input link's ctl)"; kind = "compare*"
                for _ in range(3):
                    opn = set(opened)
                    for r in roots:
                        if r in storage and re.search(r"\.lat\.", ncell(r)):
                            L = G[drv[r]]; fb = fbpins(r)
                            if any(through(w) in launch for i, w in enumerate(L["ins"]) if i not in fb): opn.add(r)
                    if opn == set(opened): break
                    opened = frozenset(opn); isl, roots, order, acyc = cone(g["ins"][q], opened)
                if not acyc: rows.append((None, name, "condition cone cyclic")); continue
        jl = None   # 2026-11-21 (B29 / B30): a latch-held condition fed by a compute. The feeder's operand latches are
        # transparent while their link's ctl is high (the B27 lesson, until now applied to compare-with-join steers only),
        # so the data term is one term per input link of the feeder: launch = that link's ctl (read by the feeder's .ujoin,
        # or by its .uor for a one-channel compare with no join), its latches opened with data pins cut (the link's
        # bundling premise), the condition latch expanded through every pin (CUTONLY), other links' latches left out
        # (each is its own term). Before 2026-11-21 08:00 UTC the data term launched at the feeder's join with every
        # operand latch counted settled there (unsound, as B27).
        if kind == "latch" and not lre.startswith("(no compute"):
            if launch:
                Ls = sorted({through(w) for j in launch for w in G[drv[j]]["ins"] if re.search(r"\.ctl\.", ncell(through(w)))})
                how = "the feeder join's input links' ctl"
            else:
                Ls = set()
                for i_ in inst:
                    for gg in G:
                        if gg["kind"] in ("lut5", "lut6") and cellof(gg) == "bridge_i.udut." + i_ + ".uor":
                            Ls |= {through(w) for w in gg["ins"] if constval(w) is None and through(w) in storage}
                Ls = sorted(Ls); how = "a joinless feeder: its input link's ctl"
            if not Ls: rows.append((None, name, "latch fed by %s: no input link ctl found" % lre)); continue
            jl = []
            for Lc in Ls:
                CUT.clear(); CUT.add(Lc); op2 = frozenset([cs]); CUTONLY = set()
                for _ in range(4):
                    i2, r2, o2, a2 = cone(g["ins"][q], op2)
                    add = {r for r in r2 if r in storage and re.search(r"\.lat\.", ncell(r)) and r != cs and
                           any(through(w) == Lc for i, w in enumerate(G[drv[r]]["ins"]) if i not in fbpins(r))}
                    if add <= set(op2): break
                    op2 = frozenset(set(op2) | add); CUTONLY = set(op2) - {cs}
                CUTONLY = set(op2) - {cs}; i2, r2, o2, a2 = cone(g["ins"][q], op2); CUT.clear(); CUTONLY = None
                if not a2: jl = None; break
                jl.append((Lc, i2, r2, o2, op2))
            if jl is None: rows.append((None, name, "condition cone cyclic (feeder term)")); continue
            launch = set(Ls)
            lre = "|".join(ncell(u) for u in Ls) + " (" + how + ")"
        if not launch and kind == "latch" and lre.startswith("(no compute"): launch = {r for r in roots if re.search(r"\.ctl\.", ncell(r))}
        if not launch: rows.append((None, name, "no launch node for %s" % lre)); continue
        def side(lset, rset, c, order=order, roots=roots, opened=opened):
            """request >= A + R (walk to lset), condition <= A + D (longest path from the roots in rset only)"""
            global launch
            launch = lset; Rv = req_bound(g["ins"][p], c)
            if Rv is None: return None
            t = {}
            for u in order:
                gg = G[drv[u]]; fb = fbpins(u) if u in opened else set()
                vals = [None if i in fb else ((0 if v in rset else None) if v in roots else t[v]) for i, v in enumerate(gg["ins"])]
                t[u] = max((x + lerp(gg["arcs"][i]["fmax"], gg["arcs"][i]["smax"], c) for i, x in enumerate(vals) if i not in fb and x is not None), default=None)
            D = t.get(g["ins"][q])
            if EXPLAIN and D is not None: explain(g, p, q, c, t, order, roots, rset, opened)
            return (Rv + lerp(g["arcs"][p]["fmin"], g["arcs"][p]["smin"], c), None if D is None else D + lerp(g["arcs"][q]["fmax"], g["arcs"][q]["smax"], c))
        if kind == "compare":
            # FIX 2026-11-20 11:15 UTC: a compare's operand latches are transparent while their link's ctl is HIGH, so they
            # change AFTER the ctl rise that the compare's join waits for; "operands settled at the join's rise" was false
            # (exit1-style suite12 lfsrfind s1: an operand latch flipped 787 ps after the join). One term per input link:
            # launch = that link's ctl (read by the join), its latches opened, their data pins cut (the link's bundling),
            # other links' latches excluded from the term (each is its own term).
            Ls = sorted({through(w) for j in launch for w in G[drv[j]]["ins"] if re.search(r"\.ctl\.", ncell(through(w)))})
            if not Ls: rows.append((None, name, "compare's join reads no link ctl: not handled")); continue
            parts = []; ISL_L = []
            for Lc in Ls:
                CUT.clear(); CUT.add(Lc); opn = frozenset()
                for _ in range(3):
                    il, rl, ol, al = cone(g["ins"][q], opn)
                    new_opn = set(opn) | {r for r in rl if r in storage and re.search(r"\.lat\.", ncell(r)) and
                                          any(through(w) == Lc for i, w in enumerate(G[drv[r]]["ins"]) if i not in fbpins(r))}
                    if new_opn == set(opn): break
                    opn = frozenset(new_opn)
                if not al: parts = None; break
                rs_ = {r for r in rl if not (r in storage and re.search(r"\.lat\.", ncell(r)))}
                parts.append(("ctl " + ncell(Lc).replace(".ctl.u.u", ""), {Lc}, rs_, ol, rl, opn)); ISL_L.append(il)
            CUT.clear()
            if parts is None: rows.append((None, name, "condition cone cyclic")); continue
            isl = set().union(*ISL_L)   # the adversary's slow class: the per-link cones (operand latches opened), not the old one
        elif kind == "compare*": parts = [("ctl", launch, roots)]   # roots: the launch ctl at A, other storage settled at A
        else:   # transparent while ctl is high: (1) from ctl's rise: the enable path through the latch; (2) from the compute's join: the data
            ctl = {r for r in roots if re.search(r"\.ctl\.", ncell(r))}
            parts = [("ctl", ctl, ctl)]
            for Lc, i2, r2, o2, op2 in (jl or []):
                isl = isl | i2
                rs_ = {r for r in r2 if not (r in storage and re.search(r"\.lat\.", ncell(r)))} - ctl
                parts.append(("feeder " + ncell(Lc).replace(".ctl.u.u", "").replace("bridge_i.udut.", ""), {Lc}, rs_ | {Lc}, o2, r2, op2))
        res, txt = [], []
        for pt in parts:
            nm_, ls, rs = pt[:3]
            rr = [side(ls, rs, c, *pt[3:]) if len(pt) > 3 else side(ls, rs, c) for c in (0, 1)]
            if any(x is None for x in rr): txt.append("%s: no forcing request path" % nm_); res = None; break
            if any(x[1] is None for x in rr): txt.append("%s: no condition path" % nm_); continue
            kk_ = min((R - D) / (R + D) for R, D in rr); res.append(kk_)
            txt.append("%s-launched slack %+.0f / %+.0f ps (kappa_lo %.3f)" % (nm_, rr[0][0] - rr[0][1], rr[1][0] - rr[1][1], kk_))
        if not res: rows.append((None, name, "%s, condition %s: %s" % (kind, cc.replace("bridge_i.udut.", ""), "; ".join(txt)))); continue
        k = min(res)
        if CLS: SC.update(isl); SA.append([names[g["out"]], q]); FA.append([names[g["out"]], p])
        rows.append((k, name, "%s, condition %s (cone %d), launch %s: %s at kappa 0 (corner 0 / 1); kappa_lo %.3f"
                     % (kind, cc.replace("bridge_i.udut.", ""), len(isl), lre.replace("\\", "").replace("bridge_i.udut.", ""), "; ".join(txt), k)))
    for k, n, t in sorted(rows, key=lambda r: (r[0] is None, r[0] if r[0] is not None else 0)): print("%-28s %s" % (n, t))
    ks = [r[0] for r in rows if r[0] is not None]
    print("steers %d, bounded %d, min kappa_lo %s" % (len(rows), len(ks), "%.3f" % min(ks) if ks else "-"))
    if PREM: print("premises: join / storage 0 at A for %d nodes (hold_mem); condition-cone roots settled at A" % len(PREM))
ONLY = sys.argv[sys.argv.index("--only") + 1] if "--only" in sys.argv else None
MUX = "--mux" in sys.argv   # also the 2-way mux joins (.uj<k>): select latch vs the select link's request line
SC, SA, FA = set(), [], []
if AUTO:
    auto()
    if CLS:
        FN = sorted(names[u] for u in WALK - SC)
        json.dump({"S": sorted(names[u] for u in SC) + SA, "F": FN + FA}, open(CLS, "w"))
        print("classes -> %s: S %d nodes + %d pins, F %d nodes + %d pins" % (CLS, len(SC), len(SA), len(FN), len(FA)))
    sys.exit(0)
print("launch %s; steer gates %d" % (sorted(ncell(u).replace("bridge_i.udut.", "") for u in launch), len(steer)))
worst = None; SC, SA, FA = set(), [], []
for gi, g in steer:
    src = [through(u) for u in g["ins"]]
    cp = [p for p, s in enumerate(src) if re.search(COND, ncell(s))]
    rp = [p for p, s in enumerate(src) if re.search(r"_j\.", ncell(s)) and p not in cp]
    if not cp or not rp: print("%s: condition pins %s request pins %s -- skipped" % (cellof(g), cp, rp)); continue
    for q in cp:
        isl, roots, order, acyc = cone(g["ins"][q])
        rk = collections.Counter(("env" if r in env else "storage" if r in storage else "other") for r in roots)
        rc = sorted(set(re.sub(r"\[\d+\]", "[]", ncell(r).replace("bridge_i.udut.", "")) for r in roots))
        if not acyc: print("%s pin %d: condition cone cyclic -- no bound" % (cellof(g), q)); continue
        SC |= isl; SA.append([names[g["out"]], q]); FA.extend([names[g["out"]], p] for p in rp)
        for p in rp:
            for c in (0, 1):
                Rv = req_bound(g["ins"][p], c); D = data_bound(g["ins"][q], order, roots, c)
                Dp = D + lerp(g["arcs"][q]["fmax"], g["arcs"][q]["smax"], c)
                if Rv is None: print("%s pin %d corner %d: no forcing request path from LAUNCH" % (cellof(g), p, c)); continue
                Rp = Rv + lerp(g["arcs"][p]["fmin"], g["arcs"][p]["smin"], c)
                k = (Rp - Dp) / (Rp + Dp)
                print("%s cond pin %d / req pin %d corner %d: request >= A + %.0f ps, condition <= A + %.0f ps (cone %d nodes, roots %s), slack %+.0f ps at kappa 0, kappa_lo %.3f"
                      % (cellof(g).replace("bridge_i.udut.", ""), q, p, c, Rp, Dp, len(isl), dict(rk), Rp - Dp, k))
                if worst is None or k < worst[0]: worst = (k, cellof(g), c)
        print("  condition cone roots (premise: settled at A): %s" % rc[:8])
if PREM: print("premises: %s" % sorted(PREM))
if worst: print("kappa_lo %.3f (%s, corner %d)" % worst)
if CLS:   # the bound's own delay assignment as simx classes: condition cone + its steer pins slow, request walk fast
    FN = sorted(names[u] for u in WALK - SC)
    json.dump({"S": sorted(names[u] for u in SC) + SA, "F": FN + FA}, open(CLS, "w"))
    print("classes -> %s: S %d nodes + %d pins, F %d nodes + %d pins (overlap dropped from F: %d)" % (CLS, len(SC), len(SA), len(FN), len(FA), len(WALK & SC)))
