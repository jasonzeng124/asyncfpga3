#!/usr/bin/env python3
"""xcheck_nextpnr.py (shard A): an INDEPENDENT check of the decoder's connectivity against nextpnr's routed JSON.

    python3 xcheck_nextpnr.py NET.json ROUTED.json

nextpnr (its own chipdb and router) says, for every placed LUT/MUXF/CARRY cell, which net each physical pin reads
and which BEL output drives that net. The decoder (read-back FASM + prjxray-db, C's walker) gives, for every gate
pin, a node; walking back through pip and site-hop gates reaches the driving primitive's output. This compares the
two, pin by pin. Neither is trusted; agreement means two different code paths derive the same connectivity.
"""
import json, sys, collections
net = json.load(open(sys.argv[1])); R = json.load(open(sys.argv[2]))["modules"]["top"]
names = net["nodes"]; gates = net["gates"]
drv = {g["out"]: gi for gi, g in enumerate(gates)}
by_name = {g["name"]: g for g in gates}


def source(n):
    seen = 0
    while True:
        gi = drv.get(n)
        if gi is None:
            return names[n]   # an undriven node: an opaque primitive output (FF, BUFG, BSCAN)
        g = gates[gi]
        if g["kind"] in ("pip", "hop"):
            n = g["ins"][0]; seen += 1
            if seen > 500:
                return "loop"
            continue
        if g["kind"] == "const":
            return "const%d" % g["init"]
        return names[g["out"]]


cdrv = {}
for cn, c in R["cells"].items():
    for p, d in c["port_directions"].items():
        if d == "output":
            for b in c["connections"][p]:
                cdrv[b] = (cn, c["type"], p, c["attributes"].get("NEXTPNR_BEL", ""))


def phys(d):
    cn, ct, p, bel = d
    if ct in ("PSEUDO_GND", "PSEUDO_VCC"):
        return "const%d" % (1 if ct == "PSEUDO_VCC" else 0)
    site, b = bel.split("/") if "/" in bel else (bel, "")
    if ct == "SLICE_LUTX":
        return "%s.%s%s" % (site, b[0], "6" if p == "O6" else "5")
    if ct == "SELMUX2_1":
        return "%s.%s" % (site, {"F7AMUX": "F7A", "F7BMUX": "F7B", "F8MUX": "F8"}[b])
    if ct == "CARRY4":
        return "%s.%s" % (site, ("CO" + p[2:]) if p.startswith("CO") else ("XOR" + p[1:]))
    if ct == "SLICE_FFX":
        return "%s.%sQ" % (site, b[0]) if b[1:] == "FF" else "%s.%s5Q" % (site, b[0])
    if ct == "BUFGCTRL":
        return "%s/O" % site
    if ct == "BSCAN":
        return "%s/%s" % (site, p)
    return "?%s/%s" % (ct, p)


stat = collections.Counter(); bad = []
for cn, c in R["cells"].items():
    ct = c["type"]; bel = c["attributes"].get("NEXTPNR_BEL", "")
    if ct == "SLICE_LUTX":
        site, b = bel.split("/")
        L, w = b[0], b[1]
        gname = "%s.%sLUT.O%s" % (site, L, w)
        pins = ["A%d" % k for k in range(1, 7 if w == "6" else 6)]
    elif ct == "SELMUX2_1":
        site, b = bel.split("/")
        gname = "%s.%s" % (site, {"F7AMUX": "F7A", "F7BMUX": "F7B", "F8MUX": "F8"}[b])
        pins = None
    elif ct == "CARRY4":
        site = bel.split("/")[0]
        gname = "%s.CARRY4.CO3" % site
        pins = "carry"
    else:
        continue
    g = by_name.get(gname)
    if g is None:
        bad.append(("no gate", cn, gname)); stat["no gate"] += 1; continue
    if pins == "carry":
        pm = {"CI": 0, "CYINIT": 1, "S0": 2, "S1": 3, "S2": 4, "S3": 5, "DI0": 6, "DI1": 7, "DI2": 8, "DI3": 9}
        items = [(p, pm[p]) for p in c["connections"] if p in pm]
    elif pins is None:
        pm = {"I0": 0, "I1": 1, "S0": 2}
        items = [(p, pm[p]) for p in c["connections"] if p in pm]
    else:
        items = [(p, int(p[1:]) - 1) for p in pins if p in c["connections"]]
    for p, k in items:
        bits = c["connections"][p]
        if not bits:
            continue
        b0 = bits[0]
        want = phys(cdrv[b0]) if b0 in cdrv else ("const%s" % b0 if b0 in ("0", "1") else "undriven")
        got = source(g["ins"][k])
        if want == got:
            stat["match"] += 1
        else:
            stat["mismatch"] += 1
            if len(bad) < 15:
                bad.append((cn[:50], gname, p, want, got))
print("xcheck:", dict(stat))
for x in bad[:15]:
    print("  ", x)
sys.exit(0 if stat["mismatch"] == 0 and stat["no gate"] == 0 else 1)
