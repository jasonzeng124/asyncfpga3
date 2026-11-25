#!/usr/bin/env python3
"""tools-B/auto/ctlrace.py MDIR STEER_REGEX OUT.json  (shard B, 2026-11-20, UNTRUSTED): the narrowest adversary for the
ctl-launched steer race (steersafe.py --auto, kind "latch"): a link stage's ctl C-element rises; its latch (transparent
while ctl is high) passes the new condition to the steer, and the same rise reaches the steer's request through the
steer's join. S (slow) = the routing from ctl to the latch's enable pin, the latch LUT, the routing from the latch to
the steer's condition pin; F (fast) = the gates of the forcing walk from the steer's request pin back to ctl (stopping
there, through the steer join by hold_mem). Everything else at mid-band. Prints both paths' gates."""
import json, re, sys
M, STEER, OUT = sys.argv[1:4]
N = json.load(open(M + "/net.json")); G = N["gates"]; names = N["nodes"]
cells = json.load(open(M + "/routed.json"))["modules"]["top"]["cells"]
bel = {v["attributes"].get("NEXTPNR_BEL"): k for k, v in cells.items()}
drv = {g["out"]: gi for gi, g in enumerate(G)}
def cellof(g):
    m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", g["name"]); return bel.get("%s/%s%sLUT" % m.groups(), "") if m else g["name"]
def ncell(u): gi = drv.get(u); return cellof(G[gi]) if gi is not None else names[u]
def chain(u):   # u back through pips / hops: [nodes], source
    out = []
    for _ in range(400):
        gi = drv.get(u)
        if gi is None or G[gi]["kind"] not in ("pip", "hop"): return out, u
        out.append(u); u = G[gi]["ins"][0]
    return out, u
storage = {g["out"] for g in G if g["kind"] in ("lut5", "lut6") and any(chain(u)[1] == g["out"] for u in g["ins"])}
def constv(u):
    s = chain(u)[1]; gi = drv.get(s)
    return gi is not None and G[gi]["kind"] == "const"
def forces0(g, q, fb):
    k = len(g["ins"]); init = int(g["init"])
    fix = {i: (1 if "VCC" in G[drv[chain(u)[1]]]["name"].upper() else 0) for i, u in enumerate(g["ins"]) if constv(u)}
    return all(not ((init >> ad) & 1) for ad in range(1 << k)
               if not (ad >> q) & 1 and not any((ad >> f) & 1 for f in fb) and all(((ad >> i) & 1) == v for i, v in fix.items()))
S, F, SP, FP = set(), set(), [], []
for gi, g in enumerate(G):
    if g["kind"] not in ("lut5", "lut6") or not re.search(STEER, cellof(g)): continue
    src = [chain(u) for u in g["ins"]]
    rp = [p for p, (c, s) in enumerate(src) if re.search(r"_j\.", ncell(s))]
    cp = [p for p, (c, s) in enumerate(src) if p not in rp and not constv(g["ins"][p]) and re.search(r"\.lat\.", ncell(s))]
    if len(rp) != 1 or len(cp) != 1: continue
    p, q = rp[0], cp[0]; lat = src[q][1]; L = G[drv[lat]]
    lsrc = [chain(u) for u in L["ins"]]
    en = [i for i, (c, s) in enumerate(lsrc) if re.search(r"\.ctl\.", ncell(s))]
    if len(en) != 1: continue
    ctl = lsrc[en[0]][1]
    S |= set(src[q][0]) | set(lsrc[en[0]][0]) | {lat}; SP.append([names[g["out"]], q])
    # request walk back to ctl
    memo = {}
    def R(u, onst=frozenset()):
        if u == ctl: return True
        if u in memo: return memo[u]
        gi2 = drv.get(u)
        if gi2 is None or u in onst: return False
        g2 = G[gi2]; fb = [i for i, w in enumerate(g2["ins"]) if g2["kind"] in ("lut5", "lut6") and chain(w)[1] == u]
        ok = False
        for i, w in enumerate(g2["ins"]):
            if i in fb or constv(w): continue
            if g2["kind"] in ("pip", "hop") or forces0(g2, i, fb):
                if R(w, onst | {u}): ok = True; F.add(u)
        memo[u] = ok; return ok
    R(g["ins"][p]); FP.append([names[g["out"]], p])
    print("%s: condition latch %s (ctl %s); S += %d routing + latch, F walk %d nodes" % (cellof(g), ncell(lat), ncell(ctl), len(src[q][0]) + len(lsrc[en[0]][0]), len(F)))
F -= S
json.dump({"S": sorted(names[u] for u in S) + SP, "F": sorted(names[u] for u in F) + FP}, open(OUT, "w"))
print("S %d nodes, F %d nodes -> %s" % (len(S), len(F), OUT))
print("F cells: %s" % sorted({ncell(u).replace("bridge_i.udut.", "") for u in F if drv.get(u) is not None and G[drv[u]]["kind"] in ("lut5", "lut6")}))
