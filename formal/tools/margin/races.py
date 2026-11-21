#!/usr/bin/env python3
"""margin/races.py (shard C, UNTRUSTED): enumerate the single-pin races of a decoded net and rank them statically.

    python3 races.py NET.json BND.json OUT.json [--latch] [--pf 4]

Candidate = (storage gate q, live pin i) as tools-B/ps/ctlsweep.py builds them: q is a logic gate (k >= 2) that
reads its own output through a copy chain; pin i is in q's INIT support and its copy-chain source s is not an env
node; the adversary arcs are q's arc on pin i plus the copy-chain hops into it. Without --latch, latch-like storage
gates (prep.py's class: some value of another pin makes q follow, feedback ignored) are left out, as ctlsweep
--control does; with --latch they are kept (rows marked latch=1).

Static rank (an ESTIMATE used only to order the simulations, not a bound): the race "pin i of q arrives late
against another way the same change reaches q". L = sum of FAST_MAX over the adversary arcs (resp. SLOW_MAX);
D = shortest path (sum of FAST_MIN, resp. SLOW_MIN, every support pin entered, the last pin's arc included) from
s (the fork) or from q's own output (the feedback race of tools-B/ps/allpaths.py) to any OTHER support pin of q,
never through q itself nor through pin i's own chain hops. kest = min over the two corners of (D - L)/(D + L):
the kappa at which, at g = 1, the slowed pin can lose to that path. Rows with no such path get kest = 1.
"""
import json, sys, heapq, argparse
ap = argparse.ArgumentParser(); ap.add_argument("net"); ap.add_argument("bnd"); ap.add_argument("out")
ap.add_argument("--latch", action="store_true"); ap.add_argument("--pf", type=float, default=4.0)
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
def latch_like(g, o):
    k, I = g["k"], g["init"]; ps = [chain(u)[0] for u in g["ins"]]
    fb = [j for j, s in enumerate(ps) if s == o and dep(g, j)]
    if not fb: return False
    fbj = fb[0]
    for p in range(k):
        if p == fbj or not dep(g, p) or ps[p] in ENV: continue
        for v in (0, 1):
            if all(((I >> x) & 1) == ((I >> (x ^ (1 << fbj))) & 1) for x in range(1 << k) if ((x >> p) & 1) == v):
                return True
    return False
fan = [[] for _ in N]
for gi, g in enumerate(G):
    if g["out"] in ENV: continue
    for p, m in enumerate(g["ins"]):
        if dep(g, p): fan[m].append((gi, p))
def dij(src, key, limit, q, ban):
    dist = {src: 0}; pq = [(0, src)]; best = {}
    while pq:
        d, m = heapq.heappop(pq)
        if d > dist.get(m, 1 << 60) or d > limit: continue
        for gi, p in fan[m]:
            nd = d + G[gi]["arcs"][p][key]
            if gi == q:
                if nd < best.get(p, 1 << 60): best[p] = nd
                continue
            o = G[gi]["out"]
            if o in ban: continue
            if nd < dist.get(o, 1 << 60) and nd <= limit: dist[o] = nd; heapq.heappush(pq, (nd, o))
    return best
rows = []; nst = nlatch = 0
for gi, g in enumerate(G):
    if is_copy(g) or g["out"] in ENV or g["k"] < 2: continue
    o = g["out"]; srcs = [chain(u) for u in g["ins"]]
    if not any(s == o for s, h in srcs): continue
    lat = latch_like(g, o); nst += 1; nlatch += lat
    if lat and not a.latch: continue
    for p, u in enumerate(g["ins"]):
        if not dep(g, p): continue
        s, hops = srcs[p]
        if s in ENV or N[s].endswith("_WIRE"): continue
        arcs = [(gi, p)] + [(drv[h], 0) for h in hops]
        LF = sum(G[x]["arcs"][y]["fmax"] for x, y in arcs); LS = sum(G[x]["arcs"][y]["smax"] for x, y in arcs)
        ban = set(hops) | {o}
        best = None
        for start, kind in ((s, "fork"),):
            if s == o: continue          # the feedback pin itself (its race is allpaths.py's)
            for key, L, c in (("fmin", LF, 0), ("smin", LS, 1)):
                bd = dij(start, key, a.pf * L + 1, gi, ban if start == s else set(hops))
                for j, D in bd.items():
                    if j == p or not dep(g, j): continue
                    k = (D - L) / (D + L)
                    if best is None or k < best[0]: best = (k, kind, j, c, D, L)
        r = dict(node=N[o], pin=p, src=N[s], latch=int(lat), fb=int(s == o),
                 arcs=[[N[G[x]["out"]], y] for x, y in arcs], name=g["name"])
        if best: r.update(kest=round(best[0], 4), via=best[1], other_pin=best[2], corner=best[3], D=best[4], L=best[5])
        else: r.update(kest=1.0, via="none")
        rows.append(r)
rows.sort(key=lambda r: r["kest"])
json.dump(rows, open(a.out, "w"), indent=0)
print("storage gates %d (latch-like %d); candidate pins %d" % (nst, nlatch, len(rows)), file=sys.stderr)
