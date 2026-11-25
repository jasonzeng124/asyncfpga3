#!/usr/bin/env python3
"""Shard C (UNTRUSTED): global bundling adversary. Latch-like storage gates (prep.py's rule: a pin p and value v
make the output independent of the feedback pin) are the data latches; for each, its data pins are its other live,
non-env, non-feedback pins. Every arc of every gate in the combinational fan-in cone of some latch data pin (through
copies and non-storage logic, stopping at storage nodes and env nodes), and NOT in the fan-in cone of any latch
enable pin, is put in class S (slow end); everything else stays fast (--cdefault F). Writes a simadv --classes JSON.
usage: bundadv.py NET BND OUT.json"""
import json, sys
net = json.load(open(sys.argv[1])); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
BJ = json.load(open(sys.argv[2])); ENV = set(idx[x] for x in BJ["env"])
drv = {g["out"]: gi for gi, g in enumerate(G) if g["out"] not in ENV}
def is_copy(g): return g["k"] == 1 and g["init"] == 2
def src(u):
    while u in drv and is_copy(G[drv[u]]): u = G[drv[u]]["ins"][0]
    return u
def dep(g, j):
    k, I = g["k"], g["init"]
    return any(((I >> x) & 1) != ((I >> (x ^ (1 << j))) & 1) for x in range(1 << k))
stor = set()
for gi, g in enumerate(G):
    if is_copy(g) or g["out"] in ENV or g["k"] < 2: continue
    if any(src(u) == g["out"] for u in g["ins"]): stor.add(g["out"])
datap, enp = [], []
for o in stor:
    g = G[drv[o]]; k, I = g["k"], g["init"]; ps = [src(u) for u in g["ins"]]
    fb = [j for j, s in enumerate(ps) if s == o and dep(g, j)]
    if not fb: continue
    fbj = fb[0]; en = None
    for p in range(k):
        if p == fbj or not dep(g, p) or ps[p] in ENV: continue
        for v in (0, 1):
            if all(((I >> x) & 1) == ((I >> (x ^ (1 << fbj))) & 1) for x in range(1 << k) if ((x >> p) & 1) == v):
                en = p
        if en is not None: break
    if en is None: continue
    for p in range(k):
        if p == fbj or not dep(g, p) or ps[p] in ENV: continue
        (enp if p == en else datap).append(g["ins"][p])
def cone(starts):
    seen = set(); st = list(starts)
    while st:
        u = st.pop()
        if u in seen or u in ENV or u not in drv: continue
        seen.add(u); g = G[drv[u]]
        if not is_copy(g) and u in stor: continue   # a storage node: its own gate is not in the cone
        for w in g["ins"]: st.append(w)
    return {u for u in seen if not (u in stor)}
D = cone(datap); E = cone(enp)
S = sorted(D - E)
print("latches with enable", len(set(datap) | set(enp)) and None, "data pins", len(datap), "enable pins", len(enp),
      "data-cone nodes", len(D), "enable-cone nodes", len(E), "slow", len(S), file=sys.stderr)
json.dump({"S": [N[u] for u in S], "F": []}, open(sys.argv[3], "w"))
