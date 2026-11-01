#!/usr/bin/env python3
"""Audit T5: compare B's ArbClean.targetQ rows (name, k, INIT, roles r1 r2 fb rst a0, tied) with my own
arbiter extraction (arb_check.py's data sources). usage: python3 -I targetq_cmp.py ArbClean.lean routed.json net.json"""
import json, re, sys
txt = open(sys.argv[1]).read()
rows = re.findall(r'\("(\S+)", (\d+), 0x([0-9a-f]+), ⟨(\d+), (\d+), (\d+), (\d+), (\d+), \[\((\d+), true\)\]⟩\)', txt)
R = json.load(open(sys.argv[2]))["modules"]["top"]["cells"]
N = json.load(open(sys.argv[3])); gn = {g["name"]: g for g in N["gates"]}
mine = {}
for cn, c in R.items():
    if not cn.endswith(".ustate$LUT6"): continue
    site, bel = c["attributes"]["NEXTPNR_BEL"].split("/")
    name = "%s.%sLUT.O6" % (site, bel[0])
    o = c["connections"]["O6"][0]
    role = {}
    for i in range(6):
        p = "A%d" % (i + 1)
        if c["connections"][p][0] == o: role["fb"] = i
        else: role[c["attributes"].get("X_ORIG_PORT_" + p, "tied")] = i
    mine[name] = (6, gn[name]["init"], (role["I0"], role["I1"], role["fb"], role["I3"], role["I4"], role["tied"]))
ok = len(rows) == 9 == len(mine)
for r in rows:
    b = (int(r[1]), int(r[2], 16), tuple(int(x) for x in r[3:9]))
    same = mine.get(r[0]) == b
    ok &= same
    print(r[0], "B:", b[0], hex(b[1]), b[2], "| mine:", mine.get(r[0]) and (mine[r[0]][0], hex(mine[r[0]][1]), mine[r[0]][2]), "OK" if same else "MISMATCH")
print("targetQ == my extraction (INIT from my decoder run, roles from nextpnr X_ORIG_PORT):", ok)
