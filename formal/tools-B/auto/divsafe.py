#!/usr/bin/env python3
"""tools-B/auto/divsafe.py MDIR [DIV] (shard B, UNTRUSTED extraction + arithmetic; the logic is Lean's
SettleAll.settle_all (data) and ChainHold.chain_hold (request)): a proved-style lower bound on the margin of ONE race
of a decoded bench route, the divider's capture at out0: the out0_data cone settles (longest path, maxima) before
out0_req can rise (the request line, minima). Island = the backward cone of out0_data, stopped at storage LUTs (a LUT
that reads its own output) and boundary nodes; it must be acyclic. Roots are listed by kind with the premise each needs.
Delays at corner c in {0, 1} (each side is linear in c): max = (1+k) lerp(fmax, smax, c), min = (1-k) lerp(fmin, smin, c);
kappa_lo = the largest k with request_min(c) >= data_max(c) at both corners, from A = joined's rise."""
import json, re, sys, collections
M = sys.argv[1]; DIV = sys.argv[2] if len(sys.argv) > 2 else "bridge_i.udut.udivui0"
N = json.load(open(M + "/net.json")); G = N["gates"]; names = N["nodes"]; idx = {n: i for i, n in enumerate(names)}
cells = json.load(open(M + "/routed.json"))["modules"]["top"]["cells"]
B = json.load(open(M + "/bnd.json"))["boundary"]
nid = lambda v: idx[v] if isinstance(v, str) else v
bel = {v["attributes"].get("NEXTPNR_BEL"): k for k, v in cells.items()}
drv = {g["out"]: gi for gi, g in enumerate(G)}
def cellof(g):
    m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", g["name"])
    return bel.get("%s/%s%sLUT" % m.groups(), "") if m else ""
def through(u):   # source through pips / hops
    for _ in range(400):
        gi = drv.get(u)
        if gi is None or G[gi]["kind"] not in ("pip", "hop"): return u
        u = G[gi]["ins"][0]
    return u
storage = set()
for gi, g in enumerate(G):
    if g["kind"] in ("lut5", "lut6") and any(through(u) == g["out"] for u in g["ins"]): storage.add(g["out"])
outs = [nid(v) for v in B["out0_data"] if not str(v).startswith("const")]
env = {nid(v) for v in json.load(open(M + "/bnd.json"))["env"]}
isl, roots = set(), set(); st = list(outs)
while st:
    u = st.pop()
    if u in isl or u in roots: continue
    gi = drv.get(u)
    if gi is None or u in storage or u in env: roots.add(u); continue
    isl.add(u); st.extend(G[gi]["ins"])
# acyclic + rank
order, state = [], {}
sys.setrecursionlimit(1000000)
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
kind = collections.Counter()
rk = {}
for r in roots:
    gi = drv.get(r); c = cellof(G[gi]) if gi is not None else ""
    k = "env:" + names[r] if r in env else ("const" if gi is not None and G[gi]["kind"] in ("const", "vcc", "gnd") else
        ("joined" if ".ujoin" in c else ("storage:" + re.sub(r"\[\d+\]", "[]", c.replace("bridge_i.udut.", ""))[:50] if r in storage else "other:" + names[r])))
    rk[r] = k; kind[re.sub(r"\[\d+\]|SLICE_X\d+Y\d+\.\w+", "*", k)] += 1
print("island: %d nodes, acyclic %s; roots %d: %s" % (len(isl), acyc, len(roots), dict(kind)))
lerp = lambda a, b, c: a + (b - a) * c
def longest(c):
    t = {}
    for u in order:
        g = G[drv[u]]; best = 0
        for p, v in enumerate(g["ins"]):
            base = 0 if v in roots else t[v]   # roots: stable / at their final value from A (premises)
            best = max(best, base + lerp(g["arcs"][p]["fmax"], g["arcs"][p]["smax"], c))
        t[u] = best
    return max(t[u] for u in outs if u in t)
# request: chain from joined through uor, udly elements (minima along the chain pin)
byc = {re.sub(r"\$LUT[56]$", "", cellof(g)): gi for gi, g in enumerate(G) if g["kind"] in ("lut5", "lut6")}
els = [byc[DIV + ".uor"]] + [byc[k] for k in sorted((c for c in byc if c.startswith(DIV + ".udly.chain.g[")), key=lambda c: int(re.search(r"g\[(\d+)\]", c).group(1)))]
jn = [r for r in roots if rk[r] == "joined"]; prev = jn[0] if jn else None
def pinsum(g, q, f):
    tot = f(g["arcs"][q]); u = g["ins"][q]
    for _ in range(400):
        gi = drv.get(u)
        if gi is None or G[gi]["kind"] not in ("pip", "hop"): return tot, u
        tot += f(G[gi]["arcs"][0]); u = G[gi]["ins"][0]
    return tot, u
req = {0: 0.0, 1: 0.0}; forced0 = True
for gi in els:
    g = G[gi]
    for c in (0, 1):
        cand = [pinsum(g, q, lambda a: lerp(a["fmin"], a["smin"], c)) for q in range(len(g["ins"]))]
        d = [t for t, s in cand if s == prev]
        if not d: sys.exit("request chain broken at %s" % cellof(g))
        req[c] += min(d)
    qs = [q for q in range(len(g["ins"])) if pinsum(g, q, lambda a: 0)[1] == prev]
    k = len(g["ins"]); init = int(g["init"])
    forced0 = forced0 and any(all(not ((init >> ad) & 1) for ad in range(1 << k) if not (ad >> q) & 1) for q in qs)
    prev = g["out"]
print("request chain: %d gates joined -> %s (= out0_req: %s); each forced to 0 by its chain pin at 0: %s" %
      (len(els), names[prev], prev == nid(B["out0_req"]), forced0))
for c in (0, 1):
    D = longest(c); R = req[c]
    print("corner %d: data settles <= A + %.0f ps (maxima); request rises >= A + %.0f ps (minima); kappa_lo %.3f" % (c, D, R, (R - D) / (R + D)))
