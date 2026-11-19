#!/usr/bin/env python3
"""tools-B/auto/divchain.py MDIR [DIVPREFIX] (shard B, UNTRUSTED arithmetic on the decoded route; the bound it feeds is
Lean's ChainHold.chain_hold_const): for a decoded bench route (MDIR = .../w/m with net.json, routed.json, bnd.json):
  data side: the divider's enable chain tp[0] -> tp[256] (cells <div>.uhold, <div>.dtap[i].u): per hop the minimum
    composite delay of the pin reading tp[i-1] (LUT pin arc + the pips / hops before it, FAST_MIN each = the band's
    floor at g = 1, kappa = 0), their sum; then the same for uq[0]'s first gate reading tp[256].
  request side: the longest SLOW_MAX path from the node `joined` drives (tp[0]'s join input) to the boundary's out0_req
    through gates reachable both ways, each gate entered once (an upper bound only for gates whose output follows the
    LAST of their inputs to rise; not proved).
Prints both in ps."""
import json, re, sys, collections
M = sys.argv[1]; DIV = sys.argv[2] if len(sys.argv) > 2 else "bridge_i.udut.udivui0"
N = json.load(open(M + "/net.json")); G = N["gates"]
cells = json.load(open(M + "/routed.json"))["modules"]["top"]["cells"]
B = json.load(open(M + "/bnd.json"))["boundary"]; names = N["nodes"]
bel = {v["attributes"].get("NEXTPNR_BEL"): k for k, v in cells.items()}
drv = {g["out"]: g for g in G}
def cellof(g):
    m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", g["name"])
    return bel.get("%s/%s%sLUT" % m.groups(), "") if m else ""
byc = {}
for g in G:
    if g["kind"] in ("lut5", "lut6"):
        cn = re.sub(r"\$LUT[56]$", "", cellof(g)); byc[cn] = g
def pinmin(g, i):   # pin arc + pips back to a LUT / non-routing gate
    tot = g["arcs"][i]["fmin"]; u = g["ins"][i]
    for _ in range(400):
        h = drv.get(u)
        if h is None or h["kind"] not in ("pip", "hop"): return tot, u
        tot += h["arcs"][0]["fmin"]; u = h["ins"][0]
    return tot, u
chain = [byc[DIV + ".uhold"]] + [byc["%s.dtap[%d].u" % (DIV, i)] for i in range(1, 257)]
tot = 0; mins = []
for i in range(1, 257):
    g = chain[i]; prev = chain[i - 1]["out"]
    c = [pinmin(g, p) for p in range(len(g["ins"]))]
    d = [t for t, s in c if s == prev]
    if not d: sys.exit("hop %d: no pin reads tp[%d]" % (i, i - 1))
    mins.append(min(d)); tot += min(d)
# readers of tp[256]
last = chain[256]["out"]; rd = []
for g in G:
    if g["kind"] in ("lut5", "lut6"):
        for p in range(len(g["ins"])):
            t, s = pinmin(g, p)
            if s == last: rd.append((t, cellof(g)))
print("data: 256 enable hops, sum of minimum pin delays %d ps (per hop min %d, median %d, max %d); + first reader of tp[256] >= %d ps (%d readers)"
      % (tot, min(mins), sorted(mins)[128], max(mins), min(t for t, _ in rd), len(rd)))
# request side: longest smax path from joined to out0_req
joined = chain[0]["ins"]; jsrc = [pinmin(chain[0], p)[1] for p in range(len(chain[0]["ins"]))]
start = None
for s in jsrc:
    h = drv.get(s)
    if h and "ujoin" in cellof(h): start = s
if start is None: start = jsrc[0]
tgt = B["out0_req"]
if isinstance(tgt, str): tgt = names.index(tgt)
rd2 = collections.defaultdict(list)
for gi, g in enumerate(G):
    for p, u in enumerate(g["ins"]): rd2[u].append((gi, p))
# forward reachable
fw = {start}; st = [start]
while st:
    u = st.pop()
    for gi, p in rd2[u]:
        o = G[gi]["out"]
        if o not in fw: fw.add(o); st.append(o)
if tgt not in fw: sys.exit("out0_req not reachable from joined")
bk = {tgt}; st = [tgt]
while st:
    u = st.pop(); h = drv.get(u)
    if h:
        for v in h["ins"]:
            if v in fw and v not in bk: bk.add(v); st.append(v)
cone = fw & bk
sys.setrecursionlimit(100000); memo = {}; onstack = set()
def lp(u):   # longest smax arrival from start to u within the cone, cycles cut
    if u == start: return 0
    if u in memo: return memo[u]
    if u in onstack: return None
    onstack.add(u); h = drv.get(u); best = None
    if h:
        for p, v in enumerate(h["ins"]):
            if v in cone:
                r = lp(v)
                if r is not None: best = max(best or 0, r + h["arcs"][p]["smax"])
    onstack.discard(u); memo[u] = best; return best
print("request: joined (%s) -> out0_req (%s): longest SLOW_MAX path %s ps through a cone of %d nodes" % (names[start], names[tgt], lp(tgt), len(cone)))

# chain_hold_side's numbers for the request (v = true): joined -> uor -> udly.chain.g[0..] -> out0_req
def pinmax(g, i):
    tot = g["arcs"][i]["smax"]; u = g["ins"][i]
    for _ in range(400):
        h = drv.get(u)
        if h is None or h["kind"] not in ("pip", "hop"): return tot, u
        tot += h["arcs"][0]["smax"]; u = h["ins"][0]
    return tot, u
els = [byc[DIV + ".uor"]] + [byc[k] for k in sorted((c for c in byc if c.startswith(DIV + ".udly.chain.g[")), key=lambda c: int(re.search(r"g\[(\d+)\]", c).group(1)))]
prev = start; SU = 0; ok = True; rows = []
for e in els:
    pins = [(pinmax(e, q), q) for q in range(len(e["ins"]))]
    cp = [(t, q) for (t, s), q in pins if s == prev]
    if not cp: rows.append("no pin of %s reads the previous node" % cellof(e)); ok = False; break
    tU, qj = cp[0]; SU += tU
    side = [(t, q) for (t, s), q in pins if s == start and q != qj]
    sw = max([t for t, _ in side], default=0)
    # ForcesP: chain pin and side pins at 1 force 1?
    k = len(e["ins"]); need = [qj] + [q for _, q in side]
    forced = all(((int(e["init"]) >> ad) & 1) for ad in range(1 << k) if all((ad >> q) & 1 for q in need))
    if sw > SU: ok = False
    rows.append("%s: chain pin %d max %d ps (sum %d), side pins %s max %d ps, forced to 1: %s" % (cellof(e).split(".")[-3:], qj, tU, SU, [q for _, q in side], sw, forced))
    ok = ok and forced; prev = e["out"]
print("request chain (chain_hold_side, v = true):"); [print("  " + r) for r in rows]
print("request at out0_req no later than join + %d ps (SLOW_MAX, kappa = 0), side conditions %s, ends at out0_req: %s" % (SU, "met" if ok else "NOT met", prev == tgt))
