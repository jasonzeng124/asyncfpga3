#!/usr/bin/env python3
"""tools-B/preload/period.py NET.json ROUTED.json DUMP.json CELLREGEX: per-iteration period from a simx dump: the rise
times of the decoded node of the one cell matching CELLREGEX (e.g. 'udut\\.umux0\\.uor$', the loop header's request
OR), consecutive differences within calls (a gap > 4x the median starts a new call); prints median / min / max ps."""
import json, re, statistics, sys
N = json.load(open(sys.argv[1])); cells = json.load(open(sys.argv[2]))["modules"]["top"]["cells"]
D = json.load(open(sys.argv[3]))["nodes"]; rx = re.compile(sys.argv[4])
m = [c for c in cells if rx.search(c)]
if len(m) != 1: sys.exit("period: %d cells match" % len(m))
b = re.match(r"^(SLICE_X\d+Y\d+)/([A-D])([56])LUT$", cells[m[0]]["attributes"]["NEXTPNR_BEL"])
o = {g["name"]: g["out"] for g in N["gates"]}["%s.%sLUT.O%s" % b.groups()]
v0, fl = D[str(o)]
rises = [t for i, t in enumerate(fl) if (v0 ^ ((i + 1) & 1)) == 1]
d = [b - a for a, b in zip(rises, rises[1:])]
med = statistics.median(d); d = [x for x in d if x < 4 * med]
print("period %s: %d iterations, median %d ps, min %d, max %d" % (m[0], len(d), statistics.median(d), min(d), max(d)))
