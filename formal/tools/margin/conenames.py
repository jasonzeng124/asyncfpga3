#!/usr/bin/env python3
"""margin/conenames.py OUT/ (shard C, UNTRUSTED naming): which design instances each capture cone of OUT/cones.json
passes through, with the cone's sweep result from OUT/margins.txt. Writes OUT/cones_named.txt.

For every cone row: the latch group (its first latch's instance), the instance prefixes (the yosys cell name up to its
first '.u' / '$' level, e.g. bridge_i.udut.uselect0) of every LUT in the cone, and the first failing kappa of that row
(or "none <= KHI"). Answers "does the search reach the capture fed by X, and where does it fail" for a named cell X.
"""
import json, os, re, sys
O = sys.argv[1]
R = json.load(open(os.path.join(O, "routed.json")))["modules"]["top"]["cells"]
bel = {c["attributes"].get("NEXTPNR_BEL"): n for n, c in R.items() if c.get("attributes", {}).get("NEXTPNR_BEL")}
def inst(node):
    m = re.match(r"(SLICE_X\d+Y\d+)\.([A-D])([56])$", node)
    if not m: return None
    return bel.get("%s/%s%sLUT" % (m.group(1), m.group(2), m.group(3)))
def prefix(nm):
    if not nm: return None
    nm = nm.replace("bridge_i.udut.", "")
    return re.split(r"\.u\b|\.u\.|\$|\.many|\.lat|\.ctl|\.udly|\.rdly|\.uack|\.udat|\.uarb", nm)[0]
fail = {}
for l in open(os.path.join(O, "margins.txt")):
    f = l.split()
    if len(f) > 4 and not l.startswith("#"):
        fail.setdefault((f[1], f[2]), []).append("%s:%s" % (f[0], f[4]))
out = []
for r in json.load(open(os.path.join(O, "cones.json"))):
    if r.get("via") != "cone": continue
    prefs = sorted(set(p for p in (prefix(inst(n)) for n, _ in r["arcs"]) if p))
    out.append("%s  %s  fails: %s\n    cone instances: %s\n" % (r["node"], inst(r["node"]) or "?", " ".join(fail.get((r["node"], str(r["pin"])), ["none"])), " ".join(prefs)))
open(os.path.join(O, "cones_named.txt"), "w").write("".join(out))
print("".join(out))
