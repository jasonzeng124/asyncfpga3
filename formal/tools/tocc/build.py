#!/usr/bin/env python3
"""Shard C helper (UNTRUSTED): collapse THE target's netlist (copy chains k=1/INIT=2) inside the kernel cone
(as simadv.py), with per-pin composite delay windows at corner 0 and 1 (g = 1, kappa = 0) and midpoint delays.
Writes model.pkl.  usage: build.py net.json bnd.json model.pkl"""
import json, sys, pickle, collections
net = json.load(open(sys.argv[1])); names = net["nodes"]; G = net["gates"]
idx = {n: i for i, n in enumerate(names)}
BJ = json.load(open(sys.argv[2])); B = BJ["boundary"]; ENV = set(idx[x] for x in BJ["env"])
drv = {}
for gi, g in enumerate(G):
    if g["out"] not in ENV: drv[g["out"]] = gi
def is_copy(g): return g["k"] == 1 and g["init"] == 2
outs = [idx[B[k]] for k in ("a_ack", "b_ack", "start_ack", "out0_req")] + [idx[x] for x in B["out0_data"]]
# collapsed cone: logic gates reachable backwards from outs through collapsed pins
def chain(u):
    """follow copy chain from node u back to its source; return (src, [arcs of copy gates])"""
    arcs = []
    while u in drv and is_copy(G[drv[u]]):
        g = G[drv[u]]; arcs.append(g["arcs"][0]); u = g["ins"][0]
    return u, arcs
def dep(g, j):
    k, I = g["k"], g["init"]
    return any(((I >> x) & 1) != ((I >> (x ^ (1 << j))) & 1) for x in range(1 << k))
gates = {}   # out node -> dict
todo = []
for o in outs:
    s, _ = chain(o); todo.append(s)
seen = set()
while todo:
    n = todo.pop()
    if n in seen: continue
    seen.add(n)
    gi = drv.get(n)
    if gi is None or n in ENV: continue
    g = G[gi]
    pins = []
    for j, u in enumerate(g["ins"]):
        s, carcs = chain(u)
        arcs = [g["arcs"][j]] + carcs
        win = {}
        for c in (0, 1):
            lo = sum((a["fmin"] if c == 0 else a["smin"]) for a in arcs)
            hi = sum((a["fmax"] if c == 0 else a["smax"]) for a in arcs)
            mid = sum(((a["fmin"] + a["fmax"]) // 2 if c == 0 else (a["smin"] + a["smax"]) // 2) for a in arcs)
            win[c] = (lo, hi, mid)
        pins.append(dict(src=s, live=dep(g, j), win=win, narcs=len(arcs), last=u))
        todo.append(s)
    gates[n] = dict(name=g["name"], k=g["k"], init=g["init"], pins=pins)
print("collapsed cone: %d logic gates, %d nodes seen" % (len(gates), len(seen)))
nb = lambda k: idx[B[k]]
bnd = {k: (idx[v] if isinstance(v, str) else [idx[x] for x in v]) for k, v in B.items()}
# resolve boundary nodes that are copies (outputs) to their sources for reading
pickle.dump(dict(names=names, gates=gates, ENV=sorted(ENV), bnd=bnd, arbs=BJ["arbs"],
                 bsrc={k: (chain(v)[0] if isinstance(v, int) else [chain(x)[0] for x in v]) for k, v in bnd.items()}),
            open(sys.argv[3], "wb"))
dup = 0
for n, g in gates.items():
    ls = [p["src"] for p in g["pins"] if p["live"]]
    if len(ls) != len(set(ls)): dup += 1
print("gates with a source on two live pins:", dup)
print("k histogram", collections.Counter(g["k"] for g in gates.values()))
