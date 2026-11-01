#!/usr/bin/env python3
"""Audit T5: the target's arbiters, extracted independently of shard A's arbs.py/D0.json.
(1) bd_arbiter state LUTs = LUT6_2 cells with INIT 64'hFFF0FFB2ACACACAC anywhere in the yosys hierarchy (synth.json);
(2) their placed BEL from nextpnr's routed.json; (3) the decoded LUT gate at that BEL in MY decoder run (net.json, T4);
(4) the feedback pin = the physical pin whose nextpnr net is the LUT's own O6 net; ins := the other 5 pin nodes;
(5) for every pin, walk the decoded 1-input copy chain back to its source and compare with nextpnr's driver cell;
(6) compare with the Lean `arbs` (lean_arbs.json from lean_vs_net.py).
usage: python3 -I arb_check.py synth.json routed.json net.json lean_arbs.json"""
import json, sys
S = json.load(open(sys.argv[1]))["modules"]
R = json.load(open(sys.argv[2]))["modules"]["top"]
N = json.load(open(sys.argv[3]))
L = json.load(open(sys.argv[4]))["arbs"]
found = []
def walk(mn, path):
    for n, c in S[mn].get("cells", {}).items():
        if c["type"] in S and S[c["type"]].get("cells"):
            walk(c["type"], path + "." + n)
        p = c.get("parameters", {})
        if c["type"] == "LUT6_2" and "INIT" in p and int(p["INIT"], 2) == 0xFFF0FFB2ACACACAC:
            found.append((path + "." + n)[1:])
walk("gcd_hw", "")
print("bd_arbiter state LUTs in the yosys hierarchy (by INIT):", len(found))
cells = R["cells"]
drv = {}
for cn, c in cells.items():
    for port, d in c.get("port_directions", {}).items():
        if d == "output":
            for b in c["connections"].get(port, []):
                drv[b] = (cn, port, c["attributes"].get("NEXTPNR_BEL"))
JN = N["nodes"]
gby = {JN[g["out"]]: g for g in N["gates"]}
gname = {g["name"]: g for g in N["gates"]}
def source(node):
    """walk 1-input copy gates (pip/hop) back to a non-copy driver or a free node"""
    seen = []
    while node in gby and gby[node]["k"] == 1 and gby[node]["init"] == 2 and gby[node]["kind"] in ("pip", "hop"):
        seen.append(node); node = JN[gby[node]["ins"][0]]
        if len(seen) > 500: return "LOOP"
    g = gby.get(node)
    return node + (" [%s %s]" % (g["kind"], g["name"]) if g else " [free]")
mine = []
ok = True
for f in sorted(found):
    cn = f + "$LUT6"
    c = cells[cn]
    site, bel = c["attributes"]["NEXTPNR_BEL"].split("/")
    g = gname["%s.%sLUT.O6" % (site, bel[0])]
    q = JN[g["out"]]
    obit = c["connections"]["O6"][0]
    pins = ["A%d" % i for i in range(1, 7)]
    fb = [i for i, p in enumerate(pins) if c["connections"].get(p, [None])[0] == obit]
    roles = {p: c["attributes"].get("X_ORIG_PORT_" + p, "const(" + str(drv.get(c["connections"].get(p, [None])[0], ("?",))[0]) + ")") for p in pins}
    insn = [JN[g["ins"][i]] for i in range(6) if i not in fb]
    mine.append({"cell": f, "q": q, "ins": insn})
    print("%s  BEL %s  decoded gate %s k=%d INIT=%x  q=%s  feedback pins=%s" % (f.replace("urig.udut.", ""), c["attributes"]["NEXTPNR_BEL"], g["name"], g["k"], g["init"], q, [pins[i] for i in fb]))
    for i, p in enumerate(pins):
        b = c["connections"].get(p, [None])[0]
        d = drv.get(b, ("?", "?", "?"))
        src = source(JN[g["ins"][i]])
        # does the decoded source agree with nextpnr's driver BEL?
        dsite = (d[2] or "").split("/")[0]
        agree = (dsite and dsite in src) or ("VCC" in d[0] and ("VCC" in src or "CONST1" in src))
        ok &= bool(agree)
        print("    %s %-4s pin node %-28s <- decoded source %-50s | nextpnr driver %s.%s @%s %s" % (
            p, roles[p], JN[g["ins"][i]], src[:50], d[0].replace("urig.udut.", "")[:45], d[1], d[2], "OK" if agree else "MISMATCH"))
    ok &= (len(fb) == 1)
print("all pin sources agree with nextpnr, exactly one feedback pin each:", ok)
ls = {a["q"]: a for a in L}
same = all(m["q"] in ls and ls[m["q"]]["ins"] == m["ins"] for m in mine) and len(L) == len(mine)
print("Lean arbs == my extraction (q and ordered ins, by node name):", same, "(%d vs %d)" % (len(L), len(mine)))
for m in mine:
    if m["q"] not in ls or ls[m["q"]]["ins"] != m["ins"]: print("   MISMATCH", m, ls.get(m["q"]))
