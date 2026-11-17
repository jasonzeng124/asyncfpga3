#!/usr/bin/env python3
"""ring_period.py (shard A, 2026-11-17; untrusted): the August ring oscillators (research/board/ro_many_aug) in formal's
delay model, from the decoded bitstream.

    python3 ring_period.py NET.json ROUTED.json MEASURED.tsv [RESEARCH_FIT.txt] > OUT.tsv

Each ring grp[g].ro[b] is a bd_delay chain of N LUT buffers closed by a NAND (`inv`), an inverting loop, so its period
is twice the loop delay. The loop is found as the shortest cycle through the ring's own LUTs and any routing (pip,
hop) gates, starting and ending at the inverter's output node; it is evaluated with every arc at FAST_MIN and at
SLOW_MAX of formal's arcs (build_net.py). b = (measured - FAST_MIN) / (SLOW_MAX - FAST_MIN) per ring, the same
definition as research's ring128 fit, so the two models' b can be compared ring by ring.
"""
import json, re, sys, heapq, collections, statistics
net = json.load(open(sys.argv[1])); N = net["nodes"]; G = net["gates"]; idx = {n: i for i, n in enumerate(N)}
cells = json.load(open(sys.argv[2]))["modules"]["top"]["cells"]
meas = {}
for l in open(sys.argv[3]):
    f = l.split()
    if f and f[0].isdigit(): meas[(int(f[0]), int(f[1]))] = (int(f[2]), float(f[3]))
rfit = {}
if len(sys.argv) > 4:
    for l in open(sys.argv[4]):
        f = l.split()
        if f and re.match(r"g\d+\.b\d+$", f[0]):
            g, b = map(int, re.findall(r"\d+", f[0])); rfit[(g, b)] = (int(f[3]), int(f[4]))
fan = collections.defaultdict(list)
for gi, g in enumerate(G):
    for p, u in enumerate(g["ins"]): fan[u].append((gi, p))
ring = collections.defaultdict(dict)
for cn, c in cells.items():
    m = re.match(r"grp\[(\d+)\]\.ro\[(\d+)\]\.(.*)", cn)
    if not m or c["type"] != "SLICE_LUTX": continue
    bm = re.match(r"(SLICE_X\d+Y\d+)/([A-D])([56])LUT", c["attributes"].get("NEXTPNR_BEL", ""))
    if bm: ring[(int(m.group(1)), int(m.group(2)))][m.group(3)] = "%s.%s%s" % bm.groups()
def loop(nodes, start, key):
    allowed = set(idx[n] for n in nodes)
    s = idx[start]; dist = {s: 0}; pq = [(0, s)]; best = None
    while pq:
        d, u = heapq.heappop(pq)
        if d > dist.get(u, 1 << 60): continue
        for gi, p in fan[u]:
            g = G[gi]; o = g["out"]
            if g["kind"] in ("lut6", "lut5") and o not in allowed: continue
            if g["kind"] not in ("lut6", "lut5", "pip", "hop"): continue
            nd = d + g["arcs"][p][key]
            if o == s:
                best = nd if best is None else min(best, nd); continue
            if nd < dist.get(o, 1 << 60): dist[o] = nd; heapq.heappush(pq, (nd, o))
    return best
print("ring\tlinks\tmeasured_ps\tformal_fastmin_ps\tformal_slowmax_ps\tb_formal\tresearch_fastmin_ps\tresearch_slowmax_ps\tb_research")
bf, br = [], []
for (g, b), lut in sorted(ring.items()):
    inv = lut.get("inv")
    if not inv or (g, b) not in meas: continue
    F = loop(list(lut.values()), inv, "fmin"); S = loop(list(lut.values()), inv, "smax")
    if F is None or S is None: print("g%d.b%d\tno loop found" % (g, b)); continue
    links, m = meas[(g, b)]; PF, PS = 2 * F, 2 * S
    x = (m - PF) / (PS - PF); bf.append(x)
    rf = rfit.get((g, b)); xr = (m - rf[0]) / (rf[1] - rf[0]) if rf else float("nan")
    if rf: br.append(xr)
    print("g%d.b%d\t%d\t%.1f\t%d\t%d\t%.4f\t%s\t%s\t%.4f" % (g, b, links, m, PF, PS, x, rf[0] if rf else "", rf[1] if rf else "", xr))
if bf:
    print("# formal: rings %d, b median %.4f (p05 %.4f, p95 %.4f); research: median %.4f" % (len(bf), statistics.median(bf),
          sorted(bf)[len(bf) // 20], sorted(bf)[-len(bf) // 20 - 1], statistics.median(br) if br else float("nan")), file=sys.stderr)
