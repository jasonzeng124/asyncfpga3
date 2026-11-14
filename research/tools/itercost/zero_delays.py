#!/usr/bin/env python3
"""zero_delays.py WORK ROUTED_JSON OUT_NETLIST PREFIX... -- an idealisation for bounding levers, never a design:
copy WORK/netlist_baked.v with every cell whose routed-JSON name starts with one of PREFIX (e.g.
bridge_i.udut.ucmpi1.udly.) given 1 ps arcs, and every ICBUF wire INTO those cells 1 ps.  The rest of the route is
untouched.  The new period, and the new critical cycle, say what removing those delays entirely could buy."""
import sys, re, json
W, RJ, OUT, prefs = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
j = json.load(open(RJ)); m = j["modules"]; top = [k for k in m if m[k].get("attributes", {}).get("top")] or list(m)
bels = {v["attributes"]["NEXTPNR_BEL"] for k, v in m[top[0]]["cells"].items()
        if any(k.startswith(p) for p in prefs) and "NEXTPNR_BEL" in v.get("attributes", {})}
bels |= {b.replace("5LUT", "6LUT") for b in bels}
cells = {l.split()[0] for l in open(W + "/names.map") if len(l.split()) > 1 and l.split()[1] in bels}
lines = open(W + "/netlist_baked.v").readlines()
inw = set()
for i, l in enumerate(lines):
    mm = re.match(r"\s*\w+\s*(?:#\(.*?\))?\s+(c_\d+)\s*\((.*)\);", l)
    if mm and mm.group(1) in cells:
        lines[i] = re.sub(r"\.(TA\dO[56]|TI0O|TD[01]OUT|TS0OUT)\((\d+)\)", lambda q: ".%s(1)" % q.group(1), l)
        inw |= set(re.findall(r"\((w\d+)\)", mm.group(2)))
nw = 0
for i, l in enumerate(lines):
    mm = re.match(r"\s*ICBUF #\(\.D\((\d+)\)\) ic_\d+ \(\.I\(\w+\), \.O\((w\d+)\)\);", l)
    if mm and mm.group(2) in inw:
        lines[i] = l.replace(".D(%s)" % mm.group(1), ".D(1)"); nw += 1
open(OUT, "w").writelines(lines)
print("cells zeroed: %d (of %d BELs matched), wires into them zeroed: %d" % (len(cells), len(bels), nw))
