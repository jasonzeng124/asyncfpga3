#!/usr/bin/env python3
"""Shard B (UNTRUSTED): storage gates not covered by celemtab/latchtab/arbiters that are C-elements once one pin (the
select sp) is held at a value sv (THE target's mux joins), with polarities, held pins and every pin's chain, for
CElemWinView. usage: muxjtab.py NET.json ARBS.json CELEM.json LATCH.json RESETNODE OUT.json"""
import json, sys, itertools
NETF, ARBF, CF, LF, RSTS, OUTF = sys.argv[1:7]
sys.argv = ["celemtab", NETF, ARBF, RSTS, "/dev/null"]
here = __file__.rsplit("/", 1)[0]
src = open(here + "/celemtab.py").read(); exec(src[:src.index("rows = []; nst")])
cov = {r["q"] for r in json.load(open(CF))["rows"]} | {r["q"] for r in json.load(open(LF))["rows"]} | arbq
rows = []
for gi, G in enumerate(g):
    if G["k"] < 2 or gi in cov: continue
    k = G["k"]; srcs = [chain(n, G["out"]) for n in G["ins"]]
    fbs = [j for j in range(k) if srcs[j][0] == G["out"]]
    if not fbs: continue
    fb = fbs[0]; ov = {}; live = []
    for i in range(k):
        if i == fb: continue
        m = srcs[i][0]
        if isconst(m): ov[i] = cval(m)
        elif not dep(G, i) or m == RST: ov[i] = 0
        else: live.append(i)
    out = lambda v: (G["init"] >> sum(b << i for i, b in enumerate(v))) & 1
    ok = None
    for sp in live:
        for sv in (0, 1):
            ci = [i for i in live if i != sp]; ov2 = dict(ov); ov2[sp] = sv
            for pol in itertools.product([0, 1], repeat=len(ci)):
                P = dict(zip(ci, pol)); good = True
                for bits in itertools.product([0, 1], repeat=len(ci) + 1):
                    v = [0] * k
                    for i, b in ov2.items(): v[i] = b
                    for i, b in zip(ci, bits): v[i] = b
                    v[fb] = bits[-1]; e = [v[i] ^ P[i] for i in ci]; o = out(v)
                    if all(x == e[0] for x in e) and o != e[0]: good = False; break
                    if not all(x == e[0] for x in e) and o != v[fb]: good = False; break
                if good: ok = (sp, sv, ci, P, ov2); break
            if ok: break
        if ok: break
    if not ok: print("not covered:", G["name"]); continue
    sp, sv, ci, P, ov2 = ok
    rows.append(dict(q=gi, name=G["name"], k=k, fb=fb, sp=sp, ci=ci, pol=[P[i] for i in ci], ov=ov2,
                     chains=[srcs[i][1] for i in range(k)], srcs=[srcs[i][0] for i in range(k)]))
json.dump({"tool": "formal/tools-B/ps/muxjtab.py (UNTRUSTED)", "net_md5": "ddbf362e", "n": len(rows), "rows": rows}, open(OUTF, "w"))
print("mux-join rows", len(rows))
