#!/usr/bin/env python3
"""Shard B (UNTRUSTED): static race scan over EVERY flipping forcing episode (followed by a hold) of every storage node
in a simulation dump. The episode's start (pin event that began the forcing) and end (pin event that ended it) are
back-traced (latest-arriving input, mid-window delays) until they meet at a common event; then the episode length is
Σd(P_end) - Σd(P_start) (P_start empty when the end traces back to the node's own flip that began the episode). The
race needs episode >= the node's feedback loop (route + pin arc). κ* = smallest κ (grid 0.005) at which P_end at the
fast end of Adm's window, P_start and the loop at the slow end violate it (current Spec.Adm: (1-κ)·lerp_lo/g ..
(1+κ)·lerp_hi·g). usage: kstar2.py NET.json DUMP.json [corner g [maxhops]]"""
import json, sys, os
from bisect import bisect_right
NETF, DUMPF = sys.argv[1:3]; c = float(sys.argv[3]) if len(sys.argv) > 3 else 0.5; G = float(sys.argv[4]) if len(sys.argv) > 4 else 1.0
MAXH = int(sys.argv[5]) if len(sys.argv) > 5 else 4000
N = json.load(open(NETF)); g = N["gates"]; D = json.load(open(DUMPF))["nodes"]
def win(e): return (1 - c) * e["fmin"] + c * e["smin"], (1 - c) * e["fmax"] + c * e["smax"]
def dmid(e): lo, hi = win(e); return int(round((lo + hi) / 2))
def fast(e, k): return (1 - k) * win(e)[0] / G
def slow(e, k): return (1 + k) * win(e)[1] * G
def hist(n): return D.get(str(n), [False, []])
def val(n, t):
    v0, ts = hist(n); return v0 ^ (bisect_right(ts, t) % 2 == 1) if t >= 0 else v0
def trace(n, t, stop_node=None, stop_t=None):
    """back-trace 'node n flips at t'; returns list of ((node,time), arc_into_node_from_next) events, newest first"""
    ev = [(n, t)]; arcs = []
    for _ in range(MAXH):
        if stop_node is not None and n == stop_node and t == stop_t: break
        if n >= len(g) or t <= 25000: break
        Gt = g[n]; best = None
        for i, m in enumerate(Gt["ins"]):
            tr = t - dmid(Gt["arcs"][i]); ts = hist(m)[1]; k = bisect_right(ts, tr)
            if k and (best is None or ts[k - 1] > best[1]): best = (m, ts[k - 1], i)
        if best is None: break
        arcs.append((n, best[2])); n, t = best[0], best[1]; ev.append((n, t))
    return ev, arcs
res = []; nep = 0; nocommon = 0
for gi, Gt in enumerate(g):
    if Gt["k"] < 2 or str(gi) not in D: continue
    fbj, route = None, []
    for j, n in enumerate(Gt["ins"]):
        m, ch = n, []
        while m < len(g) and g[m]["k"] == 1 and m != gi and len(ch) < 60: ch.append(m); m = g[m]["ins"][0]
        if m == gi: fbj, route = j, ch; break
    if fbj is None: continue
    loop = [(m, 0) for m in route] + [(gi, fbj)]
    ds = [dmid(e) for e in Gt["arcs"]]
    pts = sorted(set((t + ds[i], i, t) for i in range(Gt["k"]) if i != fbj for t in hist(Gt["ins"][i])[1]))
    def forced(t):
        out = set()
        for fbv in (False, True):
            a = 0
            for i in range(Gt["k"]):
                b = fbv if i == fbj else val(Gt["ins"][i], t - ds[i])
                if b: a |= 1 << i
            out.add((Gt["init"] >> a) & 1)
        return out.pop() if len(out) == 1 else None
    best = None
    for k, (t, i0, ts0) in enumerate(pts):
        if t < 25000: continue
        f = forced(t)
        if f is None or f == val(gi, t - 1): continue
        for t2, i1, ts1 in pts[k + 1:]:
            if t2 == t: continue
            f2 = forced(t2)
            if f2 != f:
                if f2 is None:
                    nep += 1
                    evB, arcsB = trace(Gt["ins"][i1], ts1, gi, t)
                    PB = [(gi, i1)] + arcsB
                    if evB[-1] == (gi, t):
                        PA = []
                    else:
                        evA, arcsA = trace(Gt["ins"][i0], ts0)
                        idxA = {e: q for q, e in enumerate(evA)}
                        hit = next((q for q, e in enumerate(evB) if e in idxA), None)
                        if hit is None: nocommon += 1; break
                        PB = [(gi, i1)] + arcsB[:hit]; PA = [(gi, i0)] + arcsA[:idxA[evB[hit]]]
                    ep = t2 - t
                    ks = 9.9
                    for s in range(0, 121):
                        kk = s * 0.005
                        if sum(fast(g[m]["arcs"][p], kk) for m, p in PB) - sum(slow(g[m]["arcs"][p], kk) for m, p in PA) \
                                < sum(slow(g[m]["arcs"][p], kk) for m, p in loop):
                            ks = kk; break
                    if best is None or ks < best[0]:
                        best = (ks, ep, len(PA), len(PB), t)
                        if os.environ.get("DUMPNODE") == Gt["name"]:
                            pm = {"%d:%d" % x: 2 for x in PA}; pm.update({"%d:%d" % x: -1 for x in PB}); pm.update({"%d:%d" % x: 2 for x in loop})
                            json.dump(pm, open(os.environ["DUMPOUT"], "w"))
                            json.dump({"node": gi, "PA": PA, "PB": PB, "loop": loop, "t": t, "t2": t2}, open(os.environ["DUMPOUT"] + ".arcs.json", "w"))
                break
    if best: res.append((best[0], Gt["name"], gi) + best[1:])
res.sort()
print("episodes %d, without common ancestor (within %d hops) %d, nodes %d (corner %.2f, g %.2f)" % (nep, MAXH, nocommon, len(res), c, G))
for r in res[:15]:
    print("  kstar %s %-22s gate %d episode %d ps, |P_start| %d, |P_end| %d arcs, at %d ps" % (
        ("%.3f" % r[0]) if r[0] < 9 else ">0.6", r[1], r[2], r[3], r[4], r[5], r[6]))
