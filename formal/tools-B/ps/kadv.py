#!/usr/bin/env python3
"""Shard B (UNTRUSTED): per storage node, a static estimate of the κ at which its tightest flipping episode
(from a baseline dump) could become shorter than its feedback loop: the episode is ended by a pin event whose
causal path (back-traced through the dump) starts at the node's own flip; at corner c, that path at the fast
end of its windows, (1-κ)·lerp_lo (>= FAST_MIN/g), and the loop at the slow end, (1+κ)·lerp_hi (<= SLOW_MAX·g).
kstar = smallest κ (grid 0.005) with path_fast(κ) + (reads) < loop_slow(κ). usage: kstar.py NET.json DUMP.json [c g]
kadv variant (B, 2026-11-02): kadv.py NET DUMP c g NODE OUT_posmap.json -- same analysis for one storage node,
writes its tightest causal path (value -1, fast end) and its feedback loop (value 2, slow end) as a per-pin posmap."""
import json, sys
from bisect import bisect_right
NETF, DUMPF = sys.argv[1:3]; c = float(sys.argv[3]) if len(sys.argv) > 3 else 0.5; G = float(sys.argv[4]) if len(sys.argv) > 4 else 1.0
N = json.load(open(NETF)); g = N["gates"]; D = json.load(open(DUMPF))["nodes"]
def win(e):
    return (1 - c) * e["fmin"] + c * e["smin"], (1 - c) * e["fmax"] + c * e["smax"]
def dmid(e): lo, hi = win(e); return int(round((lo + hi) / 2))
def fast(e, k): lo, _ = win(e); return max((1 - k) * lo, e["fmin"] / G)
def slow(e, k): _, hi = win(e); return min((1 + k) * hi, e["smax"] * G)
def hist(n): return D.get(str(n), [False, []])
def val(n, t):
    v0, ts = hist(n); return v0 ^ (bisect_right(ts, t) % 2 == 1)
def crit(n, t, tstop, target):
    """back-trace 'n flips at t' until reaching target's flip or time < tstop; returns list of (gate, pin) arcs"""
    arcs = []
    for _ in range(5000):
        if n == target or n >= len(g) or t <= tstop: return arcs, n == target
        Gt = g[n]; best = None
        for i, m in enumerate(Gt["ins"]):
            tr = t - dmid(Gt["arcs"][i]); ts = hist(m)[1]; k = bisect_right(ts, tr)
            if k and (best is None or ts[k - 1] > best[1]): best = (m, ts[k - 1], i)
        if best is None: return arcs, False
        arcs.append((n, best[2])); n, t = best[0], best[1]
    return arcs, False
res = []
ONLY = sys.argv[5]; OUTF = sys.argv[6]
for gi, Gt in enumerate(g):
    if Gt["name"] != ONLY: continue
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
    tflip = hist(gi)[1]
    best = None
    for k, (t, _) in enumerate(pts):
        if t < 25000: continue
        f = forced(t)
        if f is None or f == val(gi, t - 1): continue
        for t2, pin in pts[k + 1:]:
            f2 = forced(t2)
            if f2 != f:
                if f2 is None:
                    # the episode ends when pin `pin` read changes; back-trace that pin node's flip to gi's own flip
                    n = Gt["ins"][pin]; tn = t2 - ds[pin]
                    arcs, ok = crit(n, tn, t - 5000, gi)
                    if ok:
                        ep = (t2 - t, arcs + [(gi, pin)])
                        if best is None or ep[0] < best[0]: best = ep
                break
    if best is None: continue
    path = best[1]
    loop = [(m, 0) for m in route] + [(gi, fbj)]
    ks = None
    for s in range(0, 121):
        kk = s * 0.005
        pf = sum(fast(g[m]["arcs"][p], kk) for m, p in path)
        ls = sum(slow(g[m]["arcs"][p], kk) for m, p in loop)
        if pf < ls: ks = kk; break
    pmid = sum(dmid(g[m]["arcs"][p]) for m, p in path); lmid = sum(dmid(g[m]["arcs"][p]) for m, p in loop)
    pm = {"%d:%d" % (m, p): -1 for m, p in path}; pm.update({"%d:%d" % (m, p): 2 for m, p in loop})
    json.dump(pm, open(OUTF, "w"), indent=0)
    res.append((ks if ks is not None else 9.9, Gt["name"], best[0], pmid, lmid, len(path)))
res.sort()
print("storage nodes with a causally closed tightest episode:", len(res), "(corner %.2f, g %.2f)" % (c, G))
for r in res[:12]:
    print("  kstar %s  %-22s episode %d ps, causal path mid %d ps (%d arcs), loop mid %d ps" % (
        ("%.3f" % r[0]) if r[0] < 9 else ">0.6", r[1], r[2], r[3], r[5], r[4]))
