#!/usr/bin/env python3
"""tools-B/preload/zeroline.py NET.json ROUTED.json OUT.json CELLREGEX [SCALE] (shard B, UNTRUSTED what-if):
scale (default 0) the delay of a matched-delay line ON THE SAME ROUTE: every arc of the decoded LUT gates placed for the
yosys cells matching CELLREGEX (e.g. 'uaddi0\\.udly\\.chain\\.g\\[\\d+\\]\\.u$'), and of the pip / hop gates on the
routes between two such LUTs (traced back from each line LUT's inputs through pips / hops to another line LUT). The
period difference against the unscaled net is what the line costs on this placement, separated from the re-placement
a rebuilt netlist brings. Not a buildable circuit (a zero-delay route does not exist); LUT arcs are floored at 20 ps (simx's
H_RUNT(20) refuses a LUT pin whose upper bound is below w), so 'zero' leaves 12 x 20 ps."""
import json, re, sys
N = json.load(open(sys.argv[1])); cells = json.load(open(sys.argv[2]))["modules"]["top"]["cells"]
rx = re.compile(sys.argv[4]); sc = float(sys.argv[5]) if len(sys.argv) > 5 else 0.0
G = N["gates"]; byname = {g["name"]: gi for gi, g in enumerate(G)}; drv = {g["out"]: gi for gi, g in enumerate(G)}
line = set()
for cn, c in cells.items():
    if not rx.search(cn): continue
    b = re.match(r"^(SLICE_X\d+Y\d+)/([A-D])([56])LUT$", c["attributes"].get("NEXTPNR_BEL", ""))
    if b: line.add(byname["%s.%sLUT.O%s" % b.groups()])
outs = {G[gi]["out"] for gi in line}; hit = set(line)
for gi in line:
    for u in G[gi]["ins"]:
        path = []
        while u in drv and G[drv[u]]["kind"] in ("pip", "hop") and len(path) < 300: path.append(drv[u]); u = G[drv[u]]["ins"][0]
        if u in outs: hit.update(path)
for gi in hit:
    for a in G[gi]["arcs"]:
        for k in ("fmin", "fmax", "smin", "smax"):
            a[k] = int(a[k] * sc)
            if G[gi]["kind"] in ("lut5", "lut6") and a[k] < 20: a[k] = 20   # simx's H_RUNT(20) needs a LUT pin's bound >= w
json.dump(N, open(sys.argv[3], "w"))
print("zeroline: %d line LUTs, %d gates scaled by %g" % (len(line), len(hit), sc), file=sys.stderr)
