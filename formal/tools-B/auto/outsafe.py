#!/usr/bin/env python3
"""tools-B/auto/outsafe.py MDIR (shard B, UNTRUSTED extraction + arithmetic; logic = Lean SettleAll.settle_all for the
data side and ChainHold.chain_hold (v = 0) for the request side): a lower bound (kappa_lo) for the OUTPUT CAPTURE race
of any decoded bench route: out0_data settles before out0_req can rise, both counted from the rise of the storage node
J that launches out0_req (the last operator's join).
Request side: from out0_req walk back through gates; at each gate only pins that ALONE force it to 0 when at 0 count
(chain_hold's premise, checked on the INIT); R_J(u) = the largest sum of minimum composite pin delays over such paths
back to J (any such path is a valid bound; the largest is the best one). J = a storage node such a walk reaches; when
several can launch the request (a mux's joins), the bound is the smallest R_J (each launch must be covered).
Data side: the backward cone of out0_data stopped at storage LUTs / boundary nodes, acyclic; D = longest path of
maximum delays from the cone's roots, all roots counted as settled at A (premise: input latches hold from the join's
rise to the capture; J itself rises at A).
kappa_lo = min over corners c in {0, 1} of (R - D) / (R + D) (each side is linear in c at fixed kappa)."""
import json, re, sys, collections
M = sys.argv[1]
N = json.load(open(M + "/net.json")); G = N["gates"]; names = N["nodes"]; idx = {n: i for i, n in enumerate(names)}
BB = json.load(open(M + "/bnd.json")); B = BB["boundary"]; nid = lambda v: idx[v] if isinstance(v, str) else v
env = {nid(v) for v in BB["env"]}
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
storage = {g["out"] for g in G if g["kind"] in ("lut5", "lut6") and any(through(u) == g["out"] for u in g["ins"])}
lerp = lambda a, b, c: a + (b - a) * c
sys.setrecursionlimit(1000000)
def constval(u):   # a pin tied to VCC / GND (through routing): its fixed value, else None
    s = through(u); gi = drv.get(s)
    if gi is None or G[gi]["kind"] != "const": return None
    return 1 if "VCC" in G[gi]["name"].upper() else 0 if "GND" in G[gi]["name"].upper() else None
PREM = set()
def forces0(g, q, others0=False):
    """pin q at 0 forces g to 0, with constant-tied pins at their values (chain_hold_side side pins, no premise) and,
    if others0, every other non-constant pin at 0 too (side pins whose sources must be 0: a PREMISE, listed)."""
    k = len(g["ins"]); init = int(g["init"])
    fix = {i: constval(u) for i, u in enumerate(g["ins"])}
    def ok(ad):
        if (ad >> q) & 1: return False
        for i, v in fix.items():
            if v is not None and ((ad >> i) & 1) != v: return False
            if v is None and others0 and i != q and (ad >> i) & 1: return False
        return True
    return all(not ((init >> ad) & 1) for ad in range(1 << k) if ok(ad))
# request side
def req_bound(c):
    memo, onst = {}, set()
    def R(u):   # -> {J: best sum}
        if u in memo: return memo[u]
        if u in storage: return {u: 0.0}
        gi = drv.get(u)
        if gi is None or u in env or u in onst: return {}
        onst.add(u); g = G[gi]; out = {}
        single = [q for q in range(len(g["ins"])) if constval(g["ins"][q]) is None and (g["kind"] in ("pip", "hop") or forces0(g, q))]
        cand = single
        if not single and g["kind"] in ("lut5", "lut6"):   # e.g. a mux's OR of joins: the other inputs at 0 as premises
            cand = [q for q in range(len(g["ins"])) if constval(g["ins"][q]) is None and forces0(g, q, True)]
        for q in cand:
            v = g["ins"][q]
            if not single:
                for i, w in enumerate(g["ins"]):
                    if i != q and constval(w) is None: PREM.add((cellof(g).replace("bridge_i.udut.", ""), cellof(G[drv[through(w)]]).replace("bridge_i.udut.", "") if through(w) in drv else names[through(w)]))
            for J, s in R(v).items():
                t = s + lerp(g["arcs"][q]["fmin"], g["arcs"][q]["smin"], c)
                if t > out.get(J, -1): out[J] = t
        onst.discard(u); memo[u] = out; return out
    return R(nid(B["out0_req"]))
outs = [nid(v) for v in B["out0_data"] if not str(v).startswith("const")]
isl, roots = set(), set(); st = list(outs)
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
acyc = all(visit(u) for u in outs)
def data_bound(c):
    t = {}
    for u in order:
        g = G[drv[u]]
        t[u] = max((((0 if v in roots else t[v]) + lerp(g["arcs"][p]["fmax"], g["arcs"][p]["smax"], c)) for p, v in enumerate(g["ins"])), default=0)
    return max(t[u] for u in outs if u in t)
rkind = collections.Counter(("env" if r in env else ("storage" if r in storage else "other")) for r in roots)
print("data cone: %d nodes, acyclic %s, roots %s" % (len(isl), acyc, dict(rkind)))
if not acyc: sys.exit(0)
for c in (0, 1):
    Rs = req_bound(c); D = data_bound(c)
    if not Rs: print("corner %d: no forcing request chain back to a storage node" % c); continue
    J, R = min(Rs.items(), key=lambda kv: kv[1])   # every join that can launch the request must be covered: the worst one
    inc = J in roots
    if PREM: print("  premises (side pins held at 0 while the request walks): %s" % sorted(PREM)[:6])
    print("corner %d: J = %s (%s; in the data cone's roots: %s): request >= A + %.0f ps, data <= A + %.0f ps, kappa_lo %.3f"
          % (c, cellof(G[drv[J]]).replace("bridge_i.udut.", ""), names[J], inc, R, D, (R - D) / (R + D)))
