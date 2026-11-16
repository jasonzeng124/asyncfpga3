#!/usr/bin/env python3
"""margin/diverge.py (shard C, UNTRUSTED): where two simx runs of the same net part ways.

    python3 diverge.py NET.json DUMP_FAIL.json DUMP_PASS.json [--routed ROUTED.json] [--top 40]

For every node, the first index at which the two flip histories differ (a flip present in one run only, or at a
different time); the node's divergence time is the earlier of the two flip times there. Lists the earliest nodes,
LUT and cell nodes first-class: their gate, kind, and the routed (yosys) cell placed at that BEL. With the two runs
differing only in delays, the first STORAGE node (a LUT reading its own output) to diverge in a way that changes its
flip COUNT is where a race went the other way; earlier pure-timing shifts are listed too, marked "shift".
"""
import argparse, json, re
ap = argparse.ArgumentParser(); ap.add_argument("net"); ap.add_argument("a"); ap.add_argument("b")
ap.add_argument("--routed"); ap.add_argument("--top", type=int, default=40)
a = ap.parse_args()
N = json.load(open(a.net)); names = N["nodes"]; G = N["gates"]
drv = {g["out"]: g for g in G}
A = json.load(open(a.a))["nodes"]; B = json.load(open(a.b))["nodes"]
bel = {}
if a.routed:
    cells = json.load(open(a.routed))["modules"]["top"]["cells"]
    bel = {c["attributes"].get("NEXTPNR_BEL"): n for n, c in cells.items() if c.get("attributes", {}).get("NEXTPNR_BEL")}
def cellname(g):
    m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", g["name"])
    return bel.get("%s/%s%sLUT" % m.groups(), "") if m else ""
rows = []
for k in set(A) | set(B):
    va, ha = A.get(k, [False, []]); vb, hb = B.get(k, [False, []])
    if va == vb and ha == hb: continue
    i = 0
    while i < min(len(ha), len(hb)) and ha[i] == hb[i]: i += 1
    t = min(ha[i] if i < len(ha) else 1 << 62, hb[i] if i < len(hb) else 1 << 62)
    n = int(k); g = drv.get(n)
    kind = g["kind"] if g else "env/opaque"
    stor = bool(g) and g["kind"] in ("lut6", "lut5") and n in g["ins"]
    rows.append((t, n, kind, stor, len(ha), len(hb), cellname(g) if g else ""))
rows.sort()
print("# first divergence per node (FAIL run vs PASS run), earliest first; flips FAIL/PASS; storage = LUT reading its own output")
shown = 0
for t, n, kind, stor, la, lb, cn in rows:
    if kind in ("pip", "hop") and shown > 5: continue
    print("%10d  %-28s %-6s %s flips %d/%d  %s" % (t, names[n][:28], kind, "STORAGE" if stor else "       ", la, lb, cn))
    shown += 1
    if shown >= a.top: break
print("# LUT / cell nodes whose flip COUNT differs (the order of events changed there), earliest first divergence:")
cnt = [r for r in rows if r[2] not in ("pip", "hop", "env/opaque") and r[4] != r[5]]
for t, n, kind, stor, la, lb, cn in cnt[:a.top]:
    print("%10d  %-28s %-6s flips %d/%d  %s" % (t, names[n][:28], kind, la, lb, cn))
envd = [r for r in rows if r[2] == "env/opaque"]
for t, n, kind, stor, la, lb, cn in envd[:12]:
    print("env/opaque %10d  %-28s flips %d/%d" % (t, names[n][:40], la, lb))
st = [r for r in rows if r[3]]
if st:
    t, n, kind, stor, la, lb, cn = st[0]
    print("first STORAGE node to diverge: %s at %d ps (%s), flips %d vs %d" % (names[n], t, cn, la, lb))
