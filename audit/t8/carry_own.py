#!/usr/bin/env python3
"""carry_own.py (audit T8): every decoded CARRY4 CO3 gate's inputs vs nextpnr's routed CARRY4 cell.

    python3 -I carry_own.py NET.json ROUTED.json

Auditor's own code (imports nothing from formal/). For each of the decoded carry gates SLICE.CARRY4.CO3, walk
each input node back through pip/hop gates to its site source (LUT O6 'S.A6', O5 'S.A5', previous carry 'S.CO3',
constant), and compare with the driver of the matching port of nextpnr's CARRY4 cell at that site
(CIN, CYINIT, S0..S3, DI0..DI3).
"""
import json, sys
from collections import Counter

N = json.load(open(sys.argv[1]))
RJ = json.load(open(sys.argv[2]))["modules"]["top"]
names = N["nodes"]; gates = N["gates"]
drv = {g["out"]: g for g in gates}

def src(n):
    while True:
        g = drv.get(n)
        if g is None:
            return names[n]
        if g["kind"] in ("pip", "hop"):
            n = g["ins"][0]; continue
        if g["kind"] == "const":
            return "CONST%d" % g["init"]
        return names[n]

bitdrv = {}
for cn, c in RJ["cells"].items():
    for p, d in c["port_directions"].items():
        if d == "output":
            for b in c["connections"].get(p, []):
                bitdrv[b] = (cn, c, p)

def npsrc(b):
    if b in ("0", "x"): return "CONST0"
    if b == "1": return "CONST1"
    d = bitdrv.get(b)
    if d is None: return "none"
    cn, c, p = d
    bel = c["attributes"].get("NEXTPNR_BEL", "")
    site, be = bel.split("/") if "/" in bel else ("", bel)
    t = c["type"]
    if t == "SLICE_LUTX": return "%s.%s%s" % (site, be[0], be[1])
    if t == "CARRY4": return "%s.%s" % (site, p)
    if t == "PSEUDO_GND": return "CONST0"
    if t == "PSEUDO_VCC": return "CONST1"
    if t == "SLICE_FFX": return "%s.%sQ" % (site, be[:-2] if False else be)
    return "%s:%s:%s" % (t, bel, p)

carry = {}
for cn, c in RJ["cells"].items():
    if c["type"] == "CARRY4":
        carry[c["attributes"]["NEXTPNR_BEL"].split("/")[0]] = c

co3 = [g for g in gates if g["kind"] == "carry" and g["name"].endswith(".CO3")]
# decoded input order of a CO3 gate: CI, CYINIT, S0..S3, DI0..DI3 (a first guess of interleaved (S_i, DI_i) pairs
# gave 401 mismatches, all explained by the order); nextpnr calls CI 'CIN'
order = ["CIN", "CYINIT", "S0", "S1", "S2", "S3", "DI0", "DI1", "DI2", "DI3"]
res = Counter(); bad = []
for g in co3:
    site = g["name"].split(".")[0]
    c = carry.get(site)
    if c is None:
        res["no nextpnr CARRY4"] += 1; bad.append((g["name"], "no cell")); continue
    ins = [src(i) for i in g["ins"]]
    if len(ins) != len(order):
        res["arity %d" % len(ins)] += 1; bad.append((g["name"], "arity", len(ins))); continue
    for port, s in zip(order, ins):
        bits = c["connections"].get(port, [])
        e = npsrc(bits[0]) if bits else "unconnected"
        ok = s == e or (e == "unconnected" and s.startswith("CONST"))
        res["match" if ok else "mismatch"] += 1
        if not ok:
            bad.append((g["name"], port, "decoded", s, "nextpnr", e))
print("carry4 cells nextpnr", len(carry), "decoded CO3 gates", len(co3), dict(res))
for b in bad[:40]:
    print("  ", b)
