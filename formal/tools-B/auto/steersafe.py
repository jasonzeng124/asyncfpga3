#!/usr/bin/env python3
"""tools-B/auto/steersafe.py MDIR STEER COND LAUNCH  (shard B, 2026-11-20; UNTRUSTED extraction + arithmetic; logic = Lean
SettleAll.settle_all for the condition side, ChainHold.chain_hold (v = 0) and CtlChain.hold_mem (a C-element that is 0
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
M, STEER, COND, LAUNCH = sys.argv[1:5]
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
launch = {g["out"] for g in G if g["kind"] in ("lut5", "lut6") and g["out"] in storage and re.search(LAUNCH, cellof(g))}
if not steer or not launch: sys.exit("steer %d gates, launch %d storage nodes: nothing to do" % (len(steer), len(launch)))
PREM = set()
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
        onst.discard(u); memo[u] = best; return best
    return R(u0)
def cone(u0):
    isl, roots, st = set(), set(), [u0]
    while st:
        u = st.pop()
        if u in isl or u in roots: continue
        gi = drv.get(u)
        if gi is None or u in storage or u in env: roots.add(u); continue
        isl.add(u); st.extend(G[gi]["ins"])
    order, state = [], {}
    def visit(u):
        if u in roots: return True
        s = state.get(u)
        if s == 1: return False
        if s == 2: return True
        state[u] = 1
        for v in G[drv[u]]["ins"]:
            if not visit(v): return False
        state[u] = 2; order.append(u); return True
    return isl, roots, order, visit(u0)
def data_bound(u0, order, roots, c):
    t = {}
    for u in order:
        g = G[drv[u]]
        t[u] = max(((0 if v in roots else t[v]) + lerp(g["arcs"][p]["fmax"], g["arcs"][p]["smax"], c) for p, v in enumerate(g["ins"])), default=0)
    return 0 if u0 in roots else t[u0]
print("launch %s; steer gates %d" % (sorted(ncell(u).replace("bridge_i.udut.", "") for u in launch), len(steer)))
worst = None
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
