#!/usr/bin/env python3
"""Shard B (UNTRUSTED): for every latch of latchtab.py and every close of its enable in a simb.py dump, the slack of
SpecLatch.latch_close's three windows at the dump's corner c (g = 1, scatter kappa applied to the requirement only):
  width  = (open duration of the enable source before the close) - [(hi_e - lo_e) + hi_j]
  setup  = (data source stable before the close)                 - [hi_d + hi_j - lo_e]
  hold   = (data source stable after the close)                  - hi_e
(hi = (1+kappa)*lerp(SigmaFAST_MAX, SigmaSLOW_MAX, c), lo = (1-kappa)*lerp(SigmaFAST_MIN, SigmaSLOW_MIN, c)).
A latch whose data pin is tied has no setup/hold term. Closes before T0 (reset) are skipped.
usage: latchslack.py NET.json LATCH.json DUMP.json c kappa T0 [OUT.json]"""
import json, sys
from bisect import bisect_right, bisect_left
N = json.load(open(sys.argv[1])); g = N["gates"]; L = json.load(open(sys.argv[2]))
L = L["rows"] if isinstance(L, dict) else L
D = json.load(open(sys.argv[3]))["nodes"]; c = float(sys.argv[4]); K = float(sys.argv[5]); T0 = int(sys.argv[6])
def hist(n): return D.get(str(n), [False, []])
def comp(r, i, kmin, kmax):
    ch = r["chains"][i]
    a = lambda key: g[r["q"]]["arcs"][i][key] + sum(g[x]["arcs"][0][key] for x in ch)
    lo = (1 - K) * ((1 - c) * a("fmin") + c * a("smin")); hi = (1 + K) * ((1 - c) * a("fmax") + c * a("smax"))
    return lo, hi
res = []; worst = {"width": None, "setup": None, "hold": None}
for r in L:
    e, d, j = r["e"], r["d"], r["fb"]; se, sd = r["srcs"][e], r["srcs"][d]
    tied = str(d) in r["ov"] or d in r["ov"]
    loe, hie = comp(r, e, 0, 0); lod, hid = comp(r, d, 0, 0); loj, hij = comp(r, j, 0, 0)
    v0, ts = hist(se); pe = r["pe"]
    vd0, tds = hist(sd)
    # value of eff enable after toggle k: (v0 ^ (k+1)%2) ^ pe
    for k, tau in enumerate(ts):
        if tau < T0: continue
        before = (v0 ^ (k % 2 == 1)) ^ pe; after = (v0 ^ (k % 2 == 0)) ^ pe
        if not (before and not after): continue
        opened = ts[k - 1] if k > 0 else 0
        w = (tau - opened) - ((hie - loe) + hij)
        row = dict(q=r["q"], tau=tau, width=w)
        if not tied:
            i = bisect_left(tds, tau)
            lastd = tds[i - 1] if i > 0 else 0
            nextd = tds[i] if i < len(tds) else 10**12
            if nextd == tau: lastd = tau  # data toggles exactly at the close: setup 0
            row["setup"] = (tau - lastd) - (hid + hij - loe); row["hold"] = (nextd - tau) - hie
        res.append(row)
        for kk in worst:
            if kk in row and (worst[kk] is None or row[kk] < worst[kk][0]): worst[kk] = (row[kk], r["q"], r["name"], tau)
print("closes", len(res), "latches", len({x['q'] for x in res}))
for kk, v in worst.items(): print(kk, "worst slack %.0f ps at %s %s tau=%s" % v if v else "none")
if len(sys.argv) > 7: json.dump(res, open(sys.argv[7], "w"))
