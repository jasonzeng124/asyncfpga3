#!/usr/bin/env python3
"""Shard B (UNTRUSTED): per storage node, its tightest SELF-INDUCED flipping episode in a dump (kstar.py's analysis:
the end event back-traced to the node's own flip), with the path and loop as (gate, pin) lists, the corner-uniform
rational threshold (largest κ on a 0.005 grid with (1-κ)·lerp(ΣFAST_MIN,ΣSLOW_MIN,c) >= (1+κ)·lerp(ΣFAST_MAX,ΣSLOW_MAX,c)
at c = 0 and 1, g = 1), and whether every forward hop is a necessary input in that run.
usage: racetab.py NET.json DUMP.json OUT.json [corner]"""
import json, sys
from bisect import bisect_right
NETF, DUMPF, OUTF = sys.argv[1:4]; c = float(sys.argv[4]) if len(sys.argv) > 4 else 0.5
N = json.load(open(NETF)); g = N["gates"]; D = json.load(open(DUMPF))["nodes"]
def win(e): return (1 - c) * e["fmin"] + c * e["smin"], (1 - c) * e["fmax"] + c * e["smax"]
def dmid(e): lo, hi = win(e); return int(round((lo + hi) / 2))
def hist(n): return D.get(str(n), [False, []])
def val(n, t):
    v0, ts = hist(n); return v0 ^ (bisect_right(ts, t) % 2 == 1) if t >= 0 else v0
def crit(n, t, tstop, target):
    arcs = []; evs = []
    for _ in range(5000):
        if n == target or n >= len(g) or t <= tstop: return arcs, evs, n == target
        Gt = g[n]; best = None
        for i, m in enumerate(Gt["ins"]):
            tr = t - dmid(Gt["arcs"][i]); ts = hist(m)[1]; k = bisect_right(ts, tr)
            if k and (best is None or ts[k - 1] > best[1]): best = (m, ts[k - 1], i)
        if best is None: return arcs, evs, False
        arcs.append((n, best[2])); evs.append(t); n, t = best[0], best[1]
    return arcs, evs, False
def outv(G, bits): return (G["init"] >> sum(1 << i for i, b in enumerate(bits) if b)) & 1
def necessary(arcs, evs):
    for (n, pin), tn in zip(arcs, evs):
        G = g[n]; reads = [val(m, tn - dmid(G["arcs"][q])) for q, m in enumerate(G["ins"])]
        new = outv(G, reads); old = val(n, tn - 1); alt = list(reads); alt[pin] = not alt[pin]
        if not (new != old and outv(G, alt) == old): return False
    return True
def thr(path, loop):
    PF = sum(g[m]["arcs"][p]["fmin"] for m, p in path); PS = sum(g[m]["arcs"][p]["smin"] for m, p in path)
    LF = sum(g[m]["arcs"][p]["fmax"] for m, p in loop); LS = sum(g[m]["arcs"][p]["smax"] for m, p in loop)
    best = None
    for s in range(0, 201):
        k = s / 200
        if (1 - k) * PF >= (1 + k) * LF and (1 - k) * PS >= (1 + k) * LS: best = k
        else: break
    return best, (PF, PS, LF, LS)
rows = []
for gi, Gt in enumerate(g):
    if Gt["k"] < 2 or str(gi) not in D: continue
    fbj, route = None, []
    for j, n in enumerate(Gt["ins"]):
        m, ch = n, []
        while m < len(g) and g[m]["k"] == 1 and m != gi and len(ch) < 60: ch.append(m); m = g[m]["ins"][0]
        if m == gi: fbj, route = j, ch; break
    if fbj is None: continue
    ds = [dmid(e) for e in Gt["arcs"]]
    pts = sorted(set((t + ds[i], i) for i in range(Gt["k"]) if i != fbj for t in hist(Gt["ins"][i])[1]))
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
    for k, (t, _) in enumerate(pts):
        if t < 25000: continue
        f = forced(t)
        if f is None or f == val(gi, t - 1): continue
        for t2, pin in pts[k + 1:]:
            f2 = forced(t2)
            if f2 != f:
                if f2 is None:
                    arcs, evs, ok = crit(Gt["ins"][pin], t2 - ds[pin], t - 5000, gi)
                    if ok and (best is None or t2 - t < best[0]): best = (t2 - t, arcs + [(gi, pin)], evs, t)
                break
    if best is None: continue
    loop = [(m, 0) for m in route] + [(gi, fbj)]
    kt, sums = thr(best[1], loop)
    rows.append({"node": Gt["name"], "gate": gi, "episode": best[0], "t": best[3], "path": best[1], "loop": loop,
                 "kappa_all_corners": kt, "sums": sums, "necessary": necessary(best[1][:-1], best[2])})
json.dump(rows, open(OUTF, "w"))
rows.sort(key=lambda r: (r["kappa_all_corners"] if r["kappa_all_corners"] is not None else -1))
print("nodes", len(rows), "worst:", [(r["node"], r["kappa_all_corners"], r["necessary"], len(r["path"])) for r in rows[:5]])
