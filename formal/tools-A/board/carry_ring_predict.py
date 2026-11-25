#!/usr/bin/env python3
"""carry_ring_predict.py (shard A, 2026-11-17; untrusted): formal's prediction for research's CARRY4 / MUXF7 rings
(BOARD-QUEUE item 36, research/board/carry/<route>/), from the decoded bitstream, before any board run.

    python3 carry_ring_predict.py NET.json ROUTED.json PREDICTED.tsv X Y_LO Y_HI > OUT.tsv

Each ring grp[g].ro[b] (lring: LUT buffers; cring: LUTs + chained CARRY4 CIN->CO3; fring: MUXF7 selects) is closed by
its `inv` LUT. Its loop is the shortest cycle from inv's output through gates that belong to the ring: LUT, CARRY4
and MUXF gates whose output node sits at one of the ring's own BEL sites, plus any pip / site hop. The loop's arcs are
split into the CARRY / MUXF class and the rest. Period = 2 x loop (inverting loop). Columns: FAST_MIN and SLOW_MAX
periods in formal's arcs, the CARRY+MUXF part of each, and the period with the rest at band X and CARRY / MUXF at
Y_LO and Y_HI (formal's coordinates; A14 places the August LUT/routing at 0.39 for kernels, 0.465 for rings).
PREDICTED.tsv is research's own pre-registered table, echoed for comparison (P_fastmin, P_slowmax, P_x288_y02/y10).
"""
import json, re, sys, heapq, collections
net = json.load(open(sys.argv[1])); N = net["nodes"]; G = net["gates"]; idx = {n: i for i, n in enumerate(N)}
cells = json.load(open(sys.argv[2]))["modules"]["top"]["cells"]
X, YL, YH = map(float, sys.argv[4:7])
rp = {}
hdr = None
for l in open(sys.argv[3]):
    f = l.rstrip("\n").split("\t")
    if hdr is None: hdr = f; continue
    rp[f[0]] = dict(zip(hdr, f))
fan = collections.defaultdict(list)
for gi, g in enumerate(G):
    for p, u in enumerate(g["ins"]): fan[u].append((gi, p))
CELL = ("lut6", "lut5", "carry", "muxf")
ring = collections.defaultdict(lambda: {"sites": set(), "inv": None})
for cn, c in cells.items():
    m = re.match(r"grp\[(\d+)\]\.ro\[(\d+)\]\.(.*)", cn)
    if not m: continue
    bel = c["attributes"].get("NEXTPNR_BEL", "")
    r = ring[(int(m.group(1)), int(m.group(2)))]
    if "/" in bel: r["sites"].add(bel.split("/")[0])
    if m.group(3) == "inv":
        bm = re.match(r"(SLICE_X\d+Y\d+)/([A-D])([56])LUT", bel)
        r["inv"] = "%s.%s%s" % bm.groups()
def loop(sites, start):
    s = idx[start]; dist = {s: 0}; prev = {}; pq = [(0, s)]; best = None
    while pq:
        d, u = heapq.heappop(pq)
        if d > dist.get(u, 1 << 60): continue
        for gi, p in fan[u]:
            g = G[gi]; o = g["out"]
            if g["kind"] in CELL:
                if N[o].split(".")[0] not in sites: continue
            elif g["kind"] not in ("pip", "hop"): continue
            nd = d + g["arcs"][p]["fmin"]
            if o == s:
                if best is None or nd < best[0]: best = (nd, u, gi, p)
                continue
            if nd < dist.get(o, 1 << 60): dist[o] = nd; prev[o] = (u, gi, p); heapq.heappush(pq, (nd, o))
    if best is None: return None
    path = [(best[2], best[3])]; u = best[1]
    while u != s:
        pu, gi, p = prev[u]; path.append((gi, p)); u = pu
    return path
print("ring\tkind\tn\tformal_fastmin\tformal_slowmax\tformal_cy_fmin\tformal_cy_smax\tformal_x_ylo\tformal_x_yhi\t"
      "research_fastmin\tresearch_slowmax\tresearch_x288_y02\tresearch_x288_y10")
for (g, b), r in sorted(ring.items()):
    name = "g%d.b%d" % (g, b)
    if not r["inv"] or name not in rp: continue
    path = loop(r["sites"], r["inv"])
    if path is None: print(name + "\tno loop found"); continue
    F = S = cF = cS = 0
    for gi, p in path:
        a = G[gi]["arcs"][p]; F += a["fmin"]; S += a["smax"]
        if G[gi]["kind"] in ("carry", "muxf"): cF += a["fmin"]; cS += a["smax"]
    rest = (F - cF) + X * ((S - cS) - (F - cF))
    lo = 2 * (rest + cF + YL * (cS - cF)); hi = 2 * (rest + cF + YH * (cS - cF))
    q = rp[name]
    print("%s\t%s\t%s\t%d\t%d\t%d\t%d\t%.0f\t%.0f\t%s\t%s\t%s\t%s" % (name, q["kind"], q["n"], 2 * F, 2 * S, 2 * cF, 2 * cS, lo, hi,
          q["P_fastmin"], q["P_slowmax"], q["P_x288_y02"], q["P_x288_y10"]))
