#!/usr/bin/env python3
"""chainstage.py (shard A, 2026-11-17): per-stage FAST_MIN of delay-chain stages (LUT arc, routing from the previous chain LUT).
    python3 chainstage.py NET ROUTED PAT"""
import json, re, sys, statistics as st
net = json.load(open(sys.argv[1])); R = json.load(open(sys.argv[2]))["modules"]["top"]["cells"]; pat = sys.argv[3]
N = net["nodes"]; G = net["gates"]; drv = {g["out"]: gi for gi, g in enumerate(G)}; idx = {n: i for i, n in enumerate(N)}
want = set()
for cn, c in R.items():
    if re.search(pat, cn) and c["type"] == "SLICE_LUTX":
        m = re.match(r"(SLICE_X\d+Y\d+)/([A-D])([56])LUT", c["attributes"].get("NEXTPNR_BEL", ""))
        if m: want.add("%s.%s%s" % m.groups())
lut, rt, tiles = [], [], 0
for n in want:
    if n not in idx or idx[n] not in drv: continue
    g = G[drv[idx[n]]]
    if g["kind"] not in ("lut6", "lut5"): continue
    # the input that changes the output (k-input LUT; take the arc whose source chain reaches another wanted LUT)
    for p, u in enumerate(g["ins"]):
        r = 0; v = u; ok = False
        for _ in range(60):
            if v not in drv: break
            h = G[drv[v]]
            if h["kind"] in ("lut6", "lut5"):
                ok = N[v] in want; break
            if h["kind"] not in ("pip", "hop"): break
            r += h["arcs"][0]["fmin"]; v = h["ins"][0]
        if ok:
            lut.append(g["arcs"][p]["fmin"]); rt.append(r); break
print("%s: %d chain stages; per stage FAST_MIN LUT %.0f ps, routing %.0f ps (median); routing mean %.0f" % (pat, len(lut), st.median(lut), st.median(rt), st.mean(rt)))
