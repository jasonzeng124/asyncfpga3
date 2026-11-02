#!/usr/bin/env python3
"""Shard C (UNTRUSTED explorer): a one-pair run of THE target's circuit at FAST_MIN (transport), with a
sequential env (data set before the request; request rises at R + 1000, falls when all three acks are
high; out0.ack follows out0.req after DO ps). Reports transition counts and the result.
usage: witn1.py net.json bnd.json a b [R] [DO]"""
import json, sys, heapq, collections, bisect
net = json.load(open(sys.argv[1])); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
BJ = json.load(open(sys.argv[2])); B = BJ["boundary"]; ENV = set(idx[x] for x in BJ["env"])
A_, B_ = int(sys.argv[3]), int(sys.argv[4]); R = int(sys.argv[5]) if len(sys.argv) > 5 else 400000
DO = int(sys.argv[6]) if len(sys.argv) > 6 else 3000
gates = [g for g in G if g["out"] not in ENV]; drv = {g["out"]: g for g in gates}
readers = collections.defaultdict(list)
for g in gates:
    for j, u in enumerate(g["ins"]): readers[u].append((g, j))
v0 = collections.defaultdict(bool); v0[idx[B["rst"]]] = True
for bit, nm in enumerate(BJ["boundary"]["a_data"] if "a_data" in BJ["boundary"] else []): pass
bus = lambda key: [idx[x] for x in BJ["boundary"][key]]
for bit, n in enumerate(bus("a_data")):
    if n in ENV: v0[n] = bool((A_ >> bit) & 1)
for bit, n in enumerate(bus("b_data")):
    if n in ENV: v0[n] = bool((B_ >> bit) & 1)
def ev0(g):
    a = sum((1 << j) for j, u in enumerate(g["ins"]) if v0[u]); return bool((g["init"] >> a) & 1)
for it in range(1000):
    ch = 0
    for g in gates:
        v = ev0(g)
        if v0[g["out"]] != v: v0[g["out"]] = v; ch += 1
    if ch == 0: break
assert ch == 0
trans = collections.defaultdict(list)
def at(n, t):
    return v0[n] ^ (bisect.bisect_right(trans[n], t) % 2 == 1)
pq = []; inq = set()
def push(g, T):
    if (g["out"], T) not in inq: inq.add((g["out"], T)); heapq.heappush(pq, (T, 0, g["out"]))
def env_set(n, T, v):
    heapq.heappush(pq, (T, 1, n, v))
rst, req = idx[B["rst"]], idx[B["req"]]
acks = [idx[B[k]] for k in ("a_ack", "b_ack", "start_ack")]; oR, oA, pA = idx[B["out0_req"]], idx[B["out0_ack"]], idx[B["pend_ack"]]
env_set(rst, R, False); env_set(req, R + 1000, True)
state = {"req_fell": False, "result": None}
nev = 0
while pq:
    e = heapq.heappop(pq); T = e[0]; nev += 1
    if nev > 20_000_000: sys.exit("too many events")
    if e[1] == 1:
        n, v = e[2], e[3]
        if at(n, T) != v:
            trans[n].append(T)
            for h, j in readers[n]: push(h, T + h["arcs"][j]["fmin"])
            if n == req: env_set(pA, T + DO, v)     # pend.req is the shared request
        continue
    o = e[2]; inq.discard((o, T)); g = drv[o]
    a = sum((1 << j) for j, u in enumerate(g["ins"]) if at(u, T - g["arcs"][j]["fmin"]))
    v = bool((g["init"] >> a) & 1)
    if v != at(o, T):
        trans[o].append(T)
        for h, j in readers[o]: push(h, T + h["arcs"][j]["fmin"])
        # env reactions
        if o in acks and all(at(x, T) for x in acks) and at(req, T) and not state["req_fell"]:
            env_set(req, T + 1, False); state["req_fell"] = True
        if o == oR:
            if v:
                state["result"] = sum((1 << b) for b, n in enumerate(bus("out0_data")) if at(n, T + DO))
                env_set(oA, T + DO, True)
            else:
                env_set(oA, T + DO, False)
    # pend ack follows the shared request (pend.req) after DO
for T, n in []: pass
tot = sum(len(t) for t in trans.values())
moved = {n: t for n, t in trans.items() if t}
print("result", state["result"], "expected", __import__("math").gcd(A_, B_), "nodes moved", len(moved), "transitions", tot,
      "max per node", max(len(t) for t in moved.values()), "last", max(t[-1] for t in trans.values() if t))
