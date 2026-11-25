#!/usr/bin/env python3
"""selrace.py (shard A, 2026-11-16; UNTRUSTED search input): candidates for the races C's races.py does not list.

    python3 selrace.py NET.json BND.json OUT.json [--depth 1]

C's margin tool (formal/tools/margin) slows ONE route at a time, and only routes into a STORAGE gate's pin (a LUT that
reads its own output). A race whose late signal is consumed by combinational logic before it reaches storage is not
among its candidates. Research's select-arrival race (audit T116: umux0's select reaching its data-LUT select pins up to
~0.5 ns after z_req rose) is of that kind: the select route ends at a mux data LUT, which is combinational, and the
capture happens one gate later, in the next link's latch.

Candidate here = (combinational gate q, live pin i): q is a logic gate (k >= 2, not a copy, not storage) whose output
reaches, through copy chains and at most DEPTH-1 further combinational gates, a non-feedback pin of a storage gate.
The adversary arcs are q's arc on pin i plus the copy-chain hops into it, exactly as races.py builds them, and the rows
have races.py's format, so C's rank.py and margin.py run on them unchanged (same adversary: those arcs at
floor((1+k) FAST_MAX), every other arc at ceil((1-k) FAST_MIN), corner 0, g = 1).
Still a single-route adversary: a race needing two routes slow at once is not covered.
"""
import argparse, json, sys

ap = argparse.ArgumentParser(); ap.add_argument("net"); ap.add_argument("bnd"); ap.add_argument("out")
ap.add_argument("--depth", type=int, default=1)
a = ap.parse_args()
net = json.load(open(a.net)); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
ENV = set(idx[x] for x in json.load(open(a.bnd))["env"])
drv = {g["out"]: gi for gi, g in enumerate(G) if g["out"] not in ENV}


def is_copy(g): return g["k"] == 1 and g["init"] == 2


def chain(u):
    hops = []
    while u in drv and is_copy(G[drv[u]]) and len(hops) < 200:
        hops.append(u); u = G[drv[u]]["ins"][0]
    return u, hops


def dep(g, j):
    k, I = g["k"], g["init"]
    return any(((I >> x) & 1) != ((I >> (x ^ (1 << j))) & 1) for x in range(1 << k))


def logic(g): return g["k"] >= 2 and not is_copy(g) and g["out"] not in ENV


storage = set()
for gi, g in enumerate(G):
    if logic(g) and any(chain(u)[0] == g["out"] for u in g["ins"]):
        storage.add(gi)
# readers[s] = gates reading source node s through a copy chain (on a pin the gate depends on)
readers = {}
for gi, g in enumerate(G):
    if not logic(g):
        continue
    for p, u in enumerate(g["ins"]):
        if dep(g, p):
            s, _ = chain(u)
            if s != g["out"]:
                readers.setdefault(s, set()).add(gi)
# combinational gates within DEPTH of a storage gate's non-feedback pin
near = set(); frontier = set(storage)
for _ in range(a.depth):
    nxt = set()
    for gi in frontier:
        g = G[gi]
        for p, u in enumerate(g["ins"]):
            if not dep(g, p):
                continue
            s, _ = chain(u)
            if s == g["out"] or s not in drv:
                continue
            h = drv[s]
            if logic(G[h]) and h not in storage and h not in near:
                nxt.add(h)
    near |= nxt; frontier = nxt
rows = []
for gi in sorted(near):
    g = G[gi]; o = g["out"]
    for p, u in enumerate(g["ins"]):
        if not dep(g, p):
            continue
        s, hops = chain(u)
        if s in ENV or N[s].endswith("_WIRE"):
            continue
        arcs = [(gi, p)] + [(drv[h], 0) for h in hops]
        rows.append(dict(node=N[o], pin=p, src=N[s], latch=0, fb=0, comb=1,
                         feeds=sorted(N[G[r]["out"]] for r in readers.get(o, ()) if r in storage)[:8],
                         arcs=[[N[G[x]["out"]], y] for x, y in arcs], name=g["name"], kest=1.0, via="none"))
json.dump(rows, open(a.out, "w"), indent=0)
print("selrace: storage gates %d; combinational gates within depth %d: %d; candidate pins %d"
      % (len(storage), a.depth, len(near), len(rows)), file=sys.stderr)
