#!/usr/bin/env python3
"""Shard B (UNTRUSTED): storage gates of a decoded netlist that are latches in the sense of
Formal.Cells.SpecLatch.latch_close (enable pin e with polarity pe, data pin d with polarity pd, feedback j; other
pins held: sources constant gates or the reset node held low; INIT: enable open => output = data^pd, closed =>
output = feedback), and the windows latch_close derives for each, per corner c in {0,1} at g = 1, kappa = K:
  minimum open width of the enable   We >= (hi_e - lo_e) + hi_j
  data setup before the close         Wd >= hi_d + hi_j - lo_e
  data hold after the close           hi_e
(hi = (1+K)·Σmax, lo = (1-K)·Σmin over the pin's composite arcs, pin arc + copy chain).
usage: latchtab.py NET.json ARBS.json RESETNODE OUT.json [K]"""
import json, sys, itertools
sys_argv = sys.argv
NETF, ARBF, RST, OUTF = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
K = float(sys.argv[5]) if len(sys.argv) > 5 else 0.0
N = json.load(open(NETF)); g = N["gates"]; arbq = {a["qi"] for a in json.load(open(ARBF))}
drv = {G["out"]: i for i, G in enumerate(g)}
def chain(n, stop=None):
    m, ch = n, []
    while m in drv and g[drv[m]]["k"] == 1 and g[drv[m]]["init"] == 2 and m != stop and len(ch) < 80:
        ch.append(drv[m]); m = g[drv[m]]["ins"][0]
    return m, ch
def isconst(m): return m in drv and g[drv[m]]["k"] == 0
def comp(gi, i, ch, key): return g[gi]["arcs"][i][key] + sum(g[c]["arcs"][0][key] for c in ch)
rows = []; nst = 0
for gi, G in enumerate(g):
    if G["k"] < 2 or gi in arbq: continue
    k = G["k"]; srcs = [chain(n, G["out"]) for n in G["ins"]]
    fbs = [j for j in range(k) if srcs[j][0] == G["out"]]
    if not fbs: continue
    nst += 1; j = fbs[0]
    ov = {}; live = []
    for i in range(k):
        if i == j: continue
        m = srcs[i][0]
        if isconst(m): ov[i] = g[drv[m]]["init"] & 1
        elif m == RST: ov[i] = 0
        else: live.append(i)
    out = lambda v: (G["init"] >> sum(b << i for i, b in enumerate(v))) & 1
    found = None
    for e, d in itertools.permutations(live, 2):
        others = [i for i in live if i not in (e, d)]
        for pe, pd in itertools.product([0, 1], repeat=2):
            ok = True
            for bits in itertools.product([0, 1], repeat=len(live) + 1):
                v = [0] * k
                for i, b in ov.items(): v[i] = b
                for i, b in zip(live, bits): v[i] = b
                v[j] = bits[-1]
                o = out(v)
                if (v[e] ^ pe) == 1 and o != (v[d] ^ pd): ok = False; break
                if (v[e] ^ pe) == 0 and o != v[j]: ok = False; break
            if ok: found = (e, d, pe, pd); break   # other live pins: don't-care (all values enumerated)
        if found: break
    if not found: continue
    e, d, pe, pd = found
    win = []
    for kmin, kmax in [("fmin", "fmax"), ("smin", "smax")]:
        hi = lambda i: (1 + K) * comp(gi, i, srcs[i][1], kmax); lo = lambda i: (1 - K) * comp(gi, i, srcs[i][1], kmin)
        win.append(dict(We=hi(e) - lo(e) + hi(j), Wd=hi(d) + hi(j) - lo(e), hold=hi(e)))
    rows.append(dict(q=gi, name=G["name"], k=k, fb=j, e=e, d=d, pe=pe, pd=pd, ov=ov,
                     chains=[srcs[i][1] for i in range(k)], srcs=[srcs[i][0] for i in range(k)], win_fast=win[0], win_slow=win[1]))
json.dump(rows, open(OUTF, "w"))
print("storage gates (non-arbiter)", nst, "latches (latch_close sense; other live pins are don't-care)", len(rows))
for key in ["We", "Wd", "hold"]:
    vs = sorted(r["win_slow"][key] for r in rows)
    print(key, "slow corner: min %.0f median %.0f max %.0f ps" % (vs[0], vs[len(vs) // 2], vs[-1]))
