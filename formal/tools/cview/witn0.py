#!/usr/bin/env python3
"""Shard C (UNTRUSTED generator): a witness behaviour for THE theorem's circuit with an env that offers
no pair. Every arc read at delay d = FAST_MIN (Adm at g = 1, κ = 0, corner 0: read time f t = t - d).
(1) power-up values v0: a fixed point of every circuit gate under rst = 1, env idle, data 0;
(2) rst falls at R; transport simulation: gate output at T = INIT(input i at T - d_i);
(3) self-check: for every gate, at every breakpoint >= its start, out(T) = INIT(in_i(T - d_i)).
Writes JSON {v0: [nodes that are 1], trans: {node: [times]}}.   usage: witn0.py net.json bnd.json R out.json"""
import json, sys, heapq, collections, bisect
net = json.load(open(sys.argv[1])); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
BJ = json.load(open(sys.argv[2])); B = BJ["boundary"]; ENV = set(idx[x] for x in BJ["env"])
R = int(sys.argv[3]); OUT = sys.argv[4]
gates = [g for g in G if g["out"] not in ENV]
drv = {g["out"]: g for g in gates}
readers = collections.defaultdict(list)
for g in gates:
    for j, u in enumerate(g["ins"]): readers[u].append((g, j))
v0 = collections.defaultdict(bool); v0[idx[B["rst"]]] = True
def ev0(g):
    a = sum((1 << j) for j, u in enumerate(g["ins"]) if v0[u]); return bool((g["init"] >> a) & 1)
for it in range(1000):
    ch = 0
    for g in gates:
        v = ev0(g)
        if v0[g["out"]] != v: v0[g["out"]] = v; ch += 1
    if ch == 0: break
assert ch == 0, "no power-up fixed point"
trans = collections.defaultdict(list)
trans[idx[B["rst"]]] = [R]
def at(n, t):
    """value of node n at time t (piecewise constant, right-continuous at transitions)"""
    k = bisect.bisect_right(trans[n], t)
    return v0[n] ^ (k % 2 == 1)
def evalg(g, T):
    a = sum((1 << j) for j, u in enumerate(g["ins"]) if at(u, T - g["arcs"][j]["fmin"])); return bool((g["init"] >> a) & 1)
pq = []; inq = set()
def push(g, T):
    if (g["out"], T) not in inq: inq.add((g["out"], T)); heapq.heappush(pq, (T, g["out"]))
for g, j in readers[idx[B["rst"]]]: push(g, R + g["arcs"][j]["fmin"])
nev = 0
while pq:
    T, o = heapq.heappop(pq); inq.discard((o, T)); g = drv[o]; nev += 1
    if nev > 5_000_000: sys.exit("too many events")
    v = evalg(g, T)
    if v != at(o, T):
        assert not trans[o] or trans[o][-1] < T, ("non-monotone", N[o], T)
        trans[o].append(T)
        for h, j in readers[o]: push(h, T + h["arcs"][j]["fmin"])
moved = {n: ts for n, ts in trans.items() if ts}
print("events", nev, "nodes that move", len(moved), "transitions", sum(len(t) for t in moved.values()),
      "last", max(t[-1] for t in moved.values()))
# (3) self-check of every gate at every breakpoint >= start (start = max smax, g = 1, κ = 0)
bad = 0
for g in gates:
    st = max([e["smax"] for e in g["arcs"]], default=0)
    bps = {st} | {t for t in trans.get(g["out"], []) if t >= st}
    for j, u in enumerate(g["ins"]):
        bps |= {t + g["arcs"][j]["fmin"] for t in trans.get(u, []) if t + g["arcs"][j]["fmin"] >= st}
    for T in bps:
        if evalg(g, T) != at(g["out"], T): bad += 1
print("gate checks failing:", bad)
json.dump({"R": R, "v0": sorted(n for n, v in v0.items() if v), "trans": {str(n): ts for n, ts in moved.items()}}, open(OUT, "w"))
