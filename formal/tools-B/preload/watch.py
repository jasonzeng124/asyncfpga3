#!/usr/bin/env python3
"""tools-B/preload/watch.py (shard B): flip counts and first flip times of the decoded nodes of named cells in a simx dump.
    python3 watch.py NET.json ROUTED.json DUMP.json REGEX     (REGEX on the yosys cell name; LUT5 -> O5, LUT6 -> O6)"""
import json, re, sys
N = json.load(open(sys.argv[1])); cells = json.load(open(sys.argv[2]))["modules"]["top"]["cells"]
D = json.load(open(sys.argv[3]))["nodes"]; rx = re.compile(sys.argv[4])
byname = {g["name"]: g["out"] for g in N["gates"]}
for cn in sorted(cells):
    if not rx.search(cn): continue
    b = re.match(r"^(SLICE_X\d+Y\d+)/([A-D])([56])LUT$", cells[cn]["attributes"].get("NEXTPNR_BEL", ""))
    if not b: continue
    o = byname.get("%s.%sLUT.O%s" % b.groups())
    h = D.get(str(o), [False, []])
    print("%-90s v0 %d flips %4d first %s" % (cn, h[0], len(h[1]), h[1][:4]))
