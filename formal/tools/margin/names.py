#!/usr/bin/env python3
"""margin/names.py OUT/ (shard C, UNTRUSTED naming): the nextpnr cell (yosys instance) placed at each decoded LUT node
named in OUT/kappa_hi.txt and OUT/checked.txt (SITE.<L>6 -> BEL <L>6LUT, SITE.<L>5 -> <L>5LUT), from OUT/routed.json's
NEXTPNR_BEL attributes. Writes OUT/names.txt."""
import json, os, re, sys
O = sys.argv[1]
R = json.load(open(os.path.join(O, "routed.json")))["modules"]["top"]["cells"]
bel = {c["attributes"].get("NEXTPNR_BEL"): n for n, c in R.items() if c.get("attributes", {}).get("NEXTPNR_BEL")}
txt = "".join(open(os.path.join(O, f)).read() for f in ("kappa_hi.txt", "checked.txt") if os.path.exists(os.path.join(O, f)))
seen = []
for m in re.finditer(r"\b(SLICE_X\d+Y\d+)\.([A-D])([56])\b", txt):
    k = m.group(0)
    if k in seen: continue
    seen.append(k)
with open(os.path.join(O, "names.txt"), "w") as f:
    for k in seen:
        site, rest = k.split("."); b = "%s/%s%sLUT" % (site, rest[0], rest[1])
        f.write("%s  %s\n" % (k, bel.get(b, "(no cell at %s)" % b)))
print(open(os.path.join(O, "names.txt")).read())
