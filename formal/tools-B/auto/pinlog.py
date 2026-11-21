#!/usr/bin/env python3
"""tools-B/auto/pinlog.py MDIR DUMP.json STEERCELL T0 T1  (shard B, UNTRUSTED): the pin-node flips of one steer LUT (and
its output) in [T0, T1] from a simx --dump, labelled request (read from a '_j.' join) / condition (anything else live).
Tells a SETUP failure (the request pin rises, then the condition pin moves) from a HOLD failure (the condition pin
moves while the previous request is still high / just falling)."""
import json, re, sys
M, DUMP, ST, T0, T1 = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
D = json.load(open(DUMP))["nodes"]; N = json.load(open(M + "/net.json")); G = N["gates"]; names = N["nodes"]
cells = json.load(open(M + "/routed.json"))["modules"]["top"]["cells"]; bel = {v["attributes"].get("NEXTPNR_BEL"): k for k, v in cells.items()}
drv = {g["out"]: g for g in G}
def cellof(g):
    m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", g["name"]); return bel.get("%s/%s%sLUT" % m.groups(), g["name"]) if m else g["name"]
def through(u):
    for _ in range(400):
        g = drv.get(u)
        if g is None or g["kind"] not in ("pip", "hop"): return u
        u = g["ins"][0]
    return u
for g in G:
    if g["kind"] in ("lut5", "lut6") and cellof(g) == "bridge_i.udut." + ST:
        ev = []
        for p, w in enumerate(g["ins"]):
            s = through(w); sg = drv.get(s); sc = cellof(sg) if sg else names[s]
            if sg is not None and sg["kind"] == "const": continue
            v0, h = D.get(str(w), [0, []]); lab = "request" if "_j." in sc else "condition"
            val = bool(v0)
            for t in h:
                val = not val
                if T0 <= t <= T1: ev.append((t, "pin %d %-9s -> %d  (%s)" % (p, lab, val, sc.replace("bridge_i.udut.", "")[:40])))
        v0, h = D.get(str(g["out"]), [0, []]); val = bool(v0)
        for t in h:
            val = not val
            if T0 <= t <= T1: ev.append((t, "OUTPUT -> %d" % val))
        for t, s in sorted(ev): print(t, s)
