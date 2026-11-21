#!/usr/bin/env python3
"""Shard C (UNTRUSTED), margin tool: static FORK race scan over every storage node's every live input.

Race class (the gcd_ps kappa = 0.40 race, merge4 ua2 pin 0): storage gate q reads source s on pin i through route
R (copy hops + q's arc on i). If a signal launched by s's change can reach ANOTHER live pin j of q (through any
gates other than q) before s's own change arrives on pin i, q evaluates a mix of new (pin j) and stale (pin i)
inputs: an isochronic-fork / relative-timing race. Static bound per (q, i, j), at corner c in {0, 1}, g = 1:
  direct  H = sum over R of the window's slow end  (lerp(fmax, smax, c))
  detour  L = shortest path s => source of pin j (gate arcs at the window's fast end, lerp(fmin, smin, c)),
              plus pin j's route at the fast end; paths never pass through q
  fails when (1 - k) L < (1 + k) H, i.e. kappa_fork = (L - H) / (L + H) (< 0: fails at every kappa, i.e. the
  design relies on gating the static scan ignores).
Joins are passed as if any input change propagates, so the bound is pessimistic (a ranking for the adversary, not a
margin). Feedback pins (source = q) are B's allpaths class and are skipped here.
usage: forkrace.py NET.json BND.json OUT.json [--cut F] [--top N]
"""
import json, sys, heapq, argparse
ap = argparse.ArgumentParser(); ap.add_argument("net"); ap.add_argument("bnd"); ap.add_argument("out")
ap.add_argument("--cut", type=float, default=3.0, help="explore detours up to cut * H")
ap.add_argument("--top", type=int, default=60)
a = ap.parse_args()
net = json.load(open(a.net)); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
ENV = set(idx[x] for x in json.load(open(a.bnd))["env"])
drv = {g["out"]: gi for gi, g in enumerate(G) if g["out"] not in ENV}
def is_copy(g): return g["k"] == 1 and g["init"] == 2
def chain(u):
    hops = []
    while u in drv and is_copy(G[drv[u]]): hops.append(drv[u]); u = G[drv[u]]["ins"][0]
    return u, hops
def dep(g, j):
    k, I = g["k"], g["init"]
    return any(((I >> x) & 1) != ((I >> (x ^ (1 << j))) & 1) for x in range(1 << k))
def lo(e, c): return (1 - c) * e["fmin"] + c * e["smin"]
def hi(e, c): return (1 - c) * e["fmax"] + c * e["smax"]
# collapsed graph: logic gate -> per live pin (source, route arcs)
pins = {}   # gate index -> list of (pin, source node, [arcs])
succ = {}   # source node -> list of (dest gate out node, arcs)
for gi, g in enumerate(G):
    if is_copy(g) or g["out"] in ENV: continue
    lst = []
    for p, u in enumerate(g["ins"]):
        if not dep(g, p): continue
        s, hops = chain(u)
        arcs = [g["arcs"][p]] + [G[h]["arcs"][0] for h in hops]
        lst.append((p, s, arcs))
        succ.setdefault(s, []).append((g["out"], arcs))
    pins[gi] = lst
def storage(gi):
    return any(s == G[gi]["out"] for _, s, _ in pins[gi])
rows = []
for gi, lst in pins.items():
    if G[gi]["k"] < 2 or not storage(gi): continue
    q = G[gi]["out"]
    for (pi, si, ri) in lst:
        if si == q or si in ENV or N[si].endswith("_WIRE"): continue
        others = [(pj, sj, rj) for (pj, sj, rj) in lst if pj != pi and sj != q and sj != si]
        if not others: continue
        best = None
        for c in (0.0, 1.0):
            H = sum(hi(e, c) for e in ri)
            want = {}
            for pj, sj, rj in others:
                want.setdefault(sj, []).append((pj, sum(lo(e, c) for e in rj)))
            dist = {si: 0.0}; pq = [(0.0, si)]; found = {}
            lim = a.cut * H
            while pq and len(found) < len(want):
                d, u = heapq.heappop(pq)
                if d > dist.get(u, 1e18) or d > lim: continue
                if u in want and u != si: found[u] = d
                for (v, arcs) in succ.get(u, []):
                    if v == q: continue
                    nd = d + sum(lo(e, c) for e in arcs)
                    if nd < dist.get(v, 1e18): dist[v] = nd; heapq.heappush(pq, (nd, v))
            for sj, d in found.items():
                for pj, rl in want[sj]:
                    L = d + rl; k = (L - H) / (L + H)
                    if best is None or k < best[0]: best = (k, c, pj, N[sj], L, H)
        if best: rows.append({"node": N[q], "pin": pi, "src": N[si], "kappa_fork": round(best[0], 4), "corner": best[1],
                              "other_pin": best[2], "other_src": best[3], "detour_fast": round(best[4], 1), "direct_slow": round(best[5], 1)})
rows.sort(key=lambda r: r["kappa_fork"])
json.dump(rows, open(a.out, "w"), indent=0)
print("storage-pin pairs with a detour within cut:", len(rows))
for r in rows[:a.top]: print(r)
