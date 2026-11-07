#!/usr/bin/env python3
"""E8Mux: independent (untrusted, Python) per-pin ENTRY margin of the arbiter guard pins, from a
routed2x net.json + band file, by the rule of events4/ana.py / the audit's entry.py:
  margin = lo(A0->ustate) + lo(ustate) + lo(ustate->ugrant) + lo(ugrant) + lo(ugrant->ua) + lo(ua)
           - hi(A0->ua) - hi(ua)
(ua's own cell band enters per pin: lo on the guard side, hi on the late side, as Events6+).
    python3 -I entry_check.py NET.json BANDS.json
It is a cross-check of xevents8's ENTRY numbers, not a replacement (no rounding to steps)."""
import json, re, sys
net = json.load(open(sys.argv[1])); B = json.load(open(sys.argv[2]))
m = next(iter(net["modules"].values())); C = m["cells"]
drv = {}
for cn, c in C.items():
    for b in c["connections"].get("O", []):
        drv[b] = cn
def pins(cn):
    return {p: C[cn]["connections"][p][0] for p in C[cn]["connections"] if p != "O"}
def src_pin(cn, src):
    ps = [p for p, b in pins(cn).items() if drv.get(b) == src]
    return ps[0] if len(ps) == 1 else None
A = B["arcs"]; G = B["cells"]
for cn in sorted(C):
    mm = re.fullmatch(r"(.*\.uarb\d+)\.ua([12])\.u", cn)
    if not mm:
        continue
    base = mm.group(1); st = base + ".ustate$LUT6"
    if st not in C:
        continue
    ins = {p: drv.get(b) for p, b in pins(cn).items()}
    g = [d for d in ins.values() if d and d.startswith(base + ".ugrant")]
    a0 = [d for d in ins.values() if d and "_f.u.genblk1" in d]
    if len(g) != 1 or len(a0) != 1:
        continue
    g, a0 = g[0], a0[0]
    pl, pg, ps_, pgs = src_pin(cn, a0), src_pin(cn, g), src_pin(st, a0), src_pin(g, st)
    if None in (pl, pg, ps_, pgs):
        continue
    early = A[st + "/" + ps_][0] + G[st][0] + A[g + "/" + pgs][0] + G[g][0] + A[cn + "/" + pg][0] + G[cn][0]
    late = A[cn + "/" + pl][1] + G[cn][1]
    print("%5d  %s  (guard %s, A0 %s)" % (early - late, cn.replace("urig.udut.", ""), g.replace(base, ""), a0.replace("urig.udut.", "")))
