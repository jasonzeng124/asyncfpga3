#!/usr/bin/env python3
"""Shard B (UNTRUSTED): the SpecFb.fb_switch obligation on the decoded target, in simulation.
For every feedback LUT gate (an input whose copy-gate chain leads back to the gate's own output),
from a simulation dump (sim delays: corner/pos as given, transport), find every FLIPPING forcing
episode: an interval where the excitation is forced to c != the output's value before it (both feedback
values give c), followed by a hold (the excitation then depends on the feedback). fb_switch needs such an
episode to last >= the feedback loop's upper bound (route + pin arc, SLOW_MAX at g = 1). Reports the
shortest flipping episodes relative to the loop band.
usage: fbscan.py NET.json DUMP.json [corner pos [tmin]] (episodes before tmin, e.g. the reset, are skipped) """
import json, sys
from bisect import bisect_right
N = json.load(open(sys.argv[1])); D = json.load(open(sys.argv[2]))["nodes"]
c = float(sys.argv[3]) if len(sys.argv) > 3 else 0.5; p = float(sys.argv[4]) if len(sys.argv) > 4 else 0.5
TMIN = int(sys.argv[5]) if len(sys.argv) > 5 else 0
g = N["gates"]; names = N["nodes"]
def dly(e):
    lo = (1 - c) * e["fmin"] + c * e["smin"]; hi = (1 - c) * e["fmax"] + c * e["smax"]
    return int(round(lo + p * (hi - lo)))
def hist(n):
    v0, ts = D.get(str(n), [False, []]); return v0, ts
def val(n, t):
    v0, ts = hist(n); return v0 ^ (bisect_right(ts, t) % 2 == 1) if t >= 0 else v0
def chain_of(gi, j):
    m, ch = g[gi]["ins"][j], []
    while m < len(g) and g[m]["k"] == 1 and m != gi: ch.append(m); m = g[m]["ins"][0]
    return ch
res = []; nfb = 0
for gi, G in enumerate(g):
    if G["k"] < 2: continue
    fb = None
    for j, n in enumerate(G["ins"]):
        m, h, lo_, hi_ = n, 0, 0, 0
        while m < len(g) and g[m]["k"] == 1 and m != gi and h < 50:
            e = g[m]["arcs"][0]; lo_ += e["fmin"]; hi_ += e["smax"]; m = g[m]["ins"][0]; h += 1
        if m == gi:
            e = G["arcs"][j]; fb = (j, lo_ + e["fmin"], hi_ + e["smax"]); break
    if fb is None or str(gi) not in D: continue
    nfb += 1
    j, flo, fhi = fb
    ds = [dly(e) for e in G["arcs"]]
    # change points of the excitation (non-feedback pins)
    pts = sorted(set(t + ds[i] for i in range(G["k"]) if i != j for t in hist(G["ins"][i])[1]))
    def exc(t, fbv):
        a = 0
        for i in range(G["k"]):
            b = fbv if i == j else val(G["ins"][i], t - ds[i])
            if b: a |= 1 << i
        return (G["init"] >> a) & 1
    def forced(t):
        x0, x1 = exc(t, False), exc(t, True)
        return x0 if x0 == x1 else None
    for k, t in enumerate(pts):
        f = forced(t)
        if f is None: continue
        before = val(gi, t - 1)
        if f == before: continue
        # episode [t, t_end): until the next change point where forcing to f stops
        tend = None
        for t2 in pts[k + 1:]:
            if forced(t2) != f:
                tend = t2; nxt = forced(t2); break
        if tend is None: continue
        if nxt is None and t >= TMIN:   # followed by a hold: the loop must carry it
            simloop = sum(dly(g[m]["arcs"][0]) for m in chain_of(gi, j)) + ds[j]
            res.append((tend - t, fhi, flo, G["name"], t, simloop))
res.sort(key=lambda r: r[0] / r[5])
print("feedback gates with activity:", nfb, "| flipping episodes followed by a hold:", len(res))
for r in res:
    print("  episode %d ps / sim loop %d ps = %.2f  (loop band %d..%d ps)  %s at %d ps%s" % (r[0], r[5], r[0] / r[5], r[2], r[1], r[3], r[4], "   <-- SHORTER THAN LOOP SLOW_MAX" if r[0] < r[1] else ""))
print("episodes shorter than their loop's SLOW_MAX:", sum(1 for r in res if r[0] < r[1]),
      "| shorter than FAST_MIN:", sum(1 for r in res if r[0] < r[2]))
