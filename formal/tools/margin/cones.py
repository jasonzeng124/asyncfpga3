#!/usr/bin/env python3
"""margin/cones.py (shard C, UNTRUSTED): capture (setup / arrival) race candidates, one per latch group.

    python3 cones.py NET.json BND.json OUT.json [--maxarcs 200000]

The single-pin adversary (races.py) slows ONE route into a storage LUT. A bundled-data capture race is different: the
data reaching a latch is late against the latch's enable because the whole data path (the combinational cone into
the latch's data pins: datapath LUTs, carry chains, mux data LUTs and the routes of their SELECT inputs) is slow
while the request path is fast. Rule E's select-arrival race at a mux (audit T116) is such a race: the select
reaches the mux data LUTs after the mux's request has gone on.

Candidate = a latch group: the latch-like storage gates (races.py's class) whose enable pin comes from the same
source node (one link stage). Its adversary arcs = every arc of the combinational cone into the group's data pins:
from each data pin back through copy hops and non-storage gates, stopping at storage gates (latches, C-elements,
arbiters: their outputs launch the data) and at env nodes; every pin arc of every gate met, plus the data-pin arcs
of the latches themselves. The adversary (margin.py) puts these at (1+k) FAST_MAX and everything else at
(1-k) FAST_MIN: admissible at g = 1, corner 0 for every k (Spec.Adm), so any failure it finds is a behaviour; the
checkers (checkrows.py) decide that, not this file.

Rows have races.py's format with pin = 99 (marker: a cone, not a pin) and kre = 0 (no ranking: all are swept).
"""
import json, sys, argparse
ap = argparse.ArgumentParser(); ap.add_argument("net"); ap.add_argument("bnd"); ap.add_argument("out")
ap.add_argument("--maxarcs", type=int, default=200000)
a = ap.parse_args()
net = json.load(open(a.net)); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
ENV = set(idx[x] for x in json.load(open(a.bnd))["env"])
drv = {g["out"]: gi for gi, g in enumerate(G) if g["out"] not in ENV}
def is_copy(g): return g["k"] == 1 and g["init"] == 2
def chain(u):
    hops = []
    while u in drv and is_copy(G[drv[u]]) and len(hops) < 200: hops.append(u); u = G[drv[u]]["ins"][0]
    return u, hops
def dep(g, j):
    k, I = g["k"], g["init"]
    return any(((I >> x) & 1) != ((I >> (x ^ (1 << j))) & 1) for x in range(1 << k))
def holds(g, fbj, p, v):
    """with pin p at v, q's output follows only its feedback pin fbj (the latch is closed)"""
    k, I = g["k"], g["init"]
    return all(((I >> x) & 1) == ((I >> (x ^ (1 << fbj))) & 1) for x in range(1 << k) if ((x >> p) & 1) == v)
storage = set()
for gi, g in enumerate(G):
    if is_copy(g) or g["out"] in ENV or g["k"] < 2: continue
    if any(chain(u)[0] == g["out"] for u in g["ins"]): storage.add(gi)
# latch-like storage gates: enable pin(s) = pins that close the latch for some value; data pins = the rest
groups = {}
for gi in storage:
    g = G[gi]; o = g["out"]; ps = [chain(u)[0] for u in g["ins"]]
    fb = [j for j, s in enumerate(ps) if s == o and dep(g, j)]
    if not fb: continue
    fbj = fb[0]
    const = [p for p in range(g["k"]) if N[ps[p]].endswith("_WIRE")]   # VCC/GND tie-offs
    en = [p for p in range(g["k"]) if p != fbj and p not in const and dep(g, p) and ps[p] not in ENV and any(holds(g, fbj, p, v) for v in (0, 1))]
    if not en: continue
    data = [p for p in range(g["k"]) if p not in fb and p not in en and p not in const and dep(g, p)]
    if not data: continue
    key = tuple(sorted(set(ps[p] for p in en)))
    groups.setdefault(key, []).append((gi, data))
rows = []
for key, mem in groups.items():
    arcs = set(); seen = set(); stack = []
    for gi, data in mem:
        for p in data:
            arcs.add((gi, p)); stack.append(G[gi]["ins"][p])
    while stack and len(arcs) < a.maxarcs:
        u = stack.pop()
        if u in seen or u in ENV or u not in drv: continue
        seen.add(u); gj = drv[u]
        if gj in storage: continue          # a launching storage node: the cone stops at its output
        g = G[gj]
        for p, v in enumerate(g["ins"]):
            if is_copy(g) or dep(g, p): arcs.add((gj, p)); stack.append(v)
    q0 = mem[0][0]
    rows.append(dict(node=N[G[q0]["out"]], pin=99, src="+".join(N[s] for s in key), latch=1, fb=0,
                     arcs=[[N[G[x]["out"]], y] for x, y in sorted(arcs)], name="CONE(%d latches, %d arcs, %d nodes)" % (len(mem), len(arcs), len(seen)),
                     kest=0.0, via="cone", kre=0.0, members=[N[G[x]["out"]] for x, _ in mem]))
rows.sort(key=lambda r: -len(r["arcs"]))
json.dump(rows, open(a.out, "w"), indent=0)
print("storage gates %d; latch groups (one enable source) %d; cone arcs max %d, total %d" %
      (len(storage), len(rows), max((len(r["arcs"]) for r in rows), default=0), sum(len(r["arcs"]) for r in rows)), file=sys.stderr)
