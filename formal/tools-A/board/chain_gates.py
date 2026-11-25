#!/usr/bin/env python3
"""chain_gates.py (shard A, 2026-11-17): gate indices of a build's delay-chain LUTs (routed cell names matching PAT) and of the
pip/hop gates feeding them, for scale_net.py CHAIN=OUT B_CHAIN=b.   python3 chain_gates.py NET ROUTED PAT OUT"""
import json, re, sys
net = json.load(open(sys.argv[1])); R = json.load(open(sys.argv[2]))["modules"]["top"]["cells"]; pat = sys.argv[3]
N = net["nodes"]; G = net["gates"]; drv = {g["out"]: gi for gi, g in enumerate(G)}; idx = {n: i for i, n in enumerate(N)}
want = set()
for cn, c in R.items():
    if re.search(pat, cn) and c["type"] == "SLICE_LUTX":
        m = re.match(r"(SLICE_X\d+Y\d+)/([A-D])([56])LUT", c["attributes"].get("NEXTPNR_BEL", ""))
        if m: want.add("%s.%s%s" % m.groups())
out = set()
for n in want:
    if n not in idx or idx[n] not in drv: continue
    gi = drv[idx[n]]; out.add(gi)
    for u in G[gi]["ins"]:
        v = u
        for _ in range(60):
            if v not in drv or G[drv[v]]["kind"] not in ("pip", "hop"): break
            out.add(drv[v]); v = G[drv[v]]["ins"][0]
json.dump(sorted(out), open(sys.argv[4], "w")); print(len(want), "chain LUTs,", len(out), "gates")
