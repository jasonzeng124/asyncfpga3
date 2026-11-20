#!/usr/bin/env python3
"""tools-B/auto/firstpulse.py MDIR DUMP.json [N]  (shard B, UNTRUSTED): attribution of an adversary failure. From a simx
--dump, the first N narrow pulses (two output flips < 300 ps apart, after reset + 5 ns) on ANY LUT output, in time
order (STORAGE LUTs and steer outputs only: datapath glitches are normal), with the yosys cell nextpnr placed there. If a race's adversary fails, the first narrow pulse says which race
started it (e.g. the steer's output for a steer race)."""
import json, re, sys
M, DUMP = sys.argv[1], sys.argv[2]; NN = int(sys.argv[3]) if len(sys.argv) > 3 else 12
D = json.load(open(DUMP))["nodes"]; N = json.load(open(M + "/net.json")); G = N["gates"]; names = N["nodes"]
cells = json.load(open(M + "/routed.json"))["modules"]["top"]["cells"]
bel = {v["attributes"].get("NEXTPNR_BEL"): k for k, v in cells.items()}
drv = {g["out"]: g for g in G}
def through(u):
    for _ in range(400):
        g = drv.get(u)
        if g is None or g["kind"] not in ("pip", "hop"): return u
        u = g["ins"][0]
    return u
ev = []
for g in G:
    if g["kind"] not in ("lut5", "lut6"): continue
    store = any(through(w) == g["out"] for w in g["ins"])
    m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", g["name"]); c = bel.get("%s/%s%sLUT" % m.groups(), g["name"]) if m else g["name"]
    if not (store or re.search(r"ucond_br\d+\.u\$|\.uack$", c)): continue   # storage LUTs and steer outputs only
    h = D.get(str(g["out"]), [0, []])[1]
    for a, b in zip(h, h[1:]):
        if b - a < 300 and a > 405000: ev.append((a, b - a, c.replace("bridge_i.udut.", ""))); break
ev.sort()
for e in ev[:NN]: print("%d ps  width %d  %s" % e)
