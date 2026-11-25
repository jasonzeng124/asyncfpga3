#!/usr/bin/env python3
"""Shard C (UNTRUSTED explorer): static storage-node obligations on the collapsed view.
For each storage node s (a logic gate whose pin j reads its own output through routing):
  L(c)  = slow-end loop delay: sum of lerp(fmax, smax, c) over pin j's composite arcs;
  R(c)  = fast-end return delay: shortest path, by sum of lerp(fmin, smin, c) over composite
          arcs, from s's output to the source of any OTHER pin of s, through any logic gates, along pins in their INIT's support only.
A forcing episode of s that ends only as a consequence of s's own switching lasts >= R; the clean-
switch condition (SpecLoop.cgate_switch) needs >= L. kappa* = (R - L) / (R + L) is the scatter at
which (1-k)R = (1+k)L (g = 1). Episodes ended by independent events are NOT covered.
usage: loopobl.py net.json corner [out.tsv]"""
import json, sys, heapq, collections
net = json.load(open(sys.argv[1])); G = net["gates"]; N = net["nodes"]; c = float(sys.argv[2])
env_free = True
def is_copy(g): return g["k"] == 1 and g["init"] == 2
cm = {i: g["ins"][0] for i, g in enumerate(G) if is_copy(g)}
def lerp(a, b): return (1 - c) * a + c * b
def chain(u):
    arcs = []; 
    while u in cm: arcs.append(G[u]["arcs"][0]); u = cm[u]
    return u, arcs
logic = [i for i, g in enumerate(G) if not is_copy(g)]
def dep(g, j):
    k, I = g["k"], g["init"]
    return any(((I >> a) & 1) != ((I >> (a ^ (1 << j))) & 1) for a in range(1 << k))
pins = {}
for i in logic:
    g = G[i]; pins[i] = []
    for j, u in enumerate(g["ins"]):
        s, arcs = chain(u); arcs = [g["arcs"][j]] + arcs
        if not dep(g, j): continue   # pins outside the INIT's support cannot carry an effect
        pins[i].append((s, sum(lerp(a["fmin"], a["smin"]) for a in arcs), sum(lerp(a["fmax"], a["smax"]) for a in arcs)))
stor = [i for i in logic if any(s == i for s, _, _ in pins[i])]
def ctrl_pins(i):
    """Episode-ending pins: for a latch-like node, the pin(s) one value of which alone makes the
    feedback irrelevant (the enable); otherwise (C-element-like) every non-feedback support pin."""
    g = G[i]; k, I = g["k"], g["init"]
    fb = [j for j, u in enumerate(g["ins"]) if dep(g, j) and chain(u)[0] == i]
    if not fb: return []
    f = fb[0]; res = []
    inner = lambda p: chain(g["ins"][p])[0] < len(G)   # sourced by a gate (not reset/env/undriven)
    for p in range(k):
        if p == f or not dep(g, p) or not inner(p): continue
        for v in (0, 1):
            if all(((I >> a) & 1) == ((I >> (a ^ (1 << f))) & 1) for a in range(1 << k) if ((a >> p) & 1) == v):
                res.append(p); break
    if res: return res
    return [p for p in range(k) if p != f and dep(g, p) and inner(p)]
succ = collections.defaultdict(list)   # source -> (reader gate, fast delay)
for i in logic:
    for s, lo, hi in pins[i]:
        if s != i: succ[s].append((i, lo))
rows = []
for s in stor:
    L = max(hi for src, lo, hi in pins[s] if src == s)
    cp = set(ctrl_pins(s))
    targets = {chain(G[s]["ins"][p])[0] for p in cp} - {s}
    dist = {s: 0.0}; pq = [(0.0, s)]; R = None
    while pq:
        d, v = heapq.heappop(pq)
        if d > dist.get(v, 1e18): continue
        if v in targets and v != s: R = d; break
        if d > 20 * L + 20000: break
        for w, lo in succ[v]:
            nd = d + lo
            if nd < dist.get(w, 1e18): dist[w] = nd; heapq.heappush(pq, (nd, w))
    k = (R - L) / (R + L) if R is not None else None
    rows.append((k if k is not None else 9.0, N[s], L, R))
rows.sort()
print("storage nodes", len(stor), "no return path", sum(1 for r in rows if r[3] is None))
for k, n, L, R in rows[:15]: print(f"kappa* {k:+.3f}  L {L:7.1f}  R {R if R is None else round(R,1)}  {n}")
if len(sys.argv) > 3:
    with open(sys.argv[3], "w") as f:
        f.write("kappa_star\tnode\tloop_slow_ps\treturn_fast_ps\n")
        for k, n, L, R in rows: f.write(f"{k:.4f}\t{n}\t{L:.1f}\t{R}\n")
