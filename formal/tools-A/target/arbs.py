#!/usr/bin/env python3
"""arbs.py (shard A, THE goal): the target's arbiters as Spec.ArbNodes (untrusted naming).

    python3 arbs.py ROUTED.json D0.json NET.json OUT.json

For every nextpnr cell `*.uarb*.ustate$LUT6` (bd_arbiter's state LUT, O6 = q): q = the decoded node
`<site>.<L>6`; ins = the site-pin nodes of that LUT's six pins whose source is not q itself
(the feedback pin is left out).
"""
import json, sys
R = json.load(open(sys.argv[1]))["modules"]["top"]
D = json.load(open(sys.argv[2]))
N = json.load(open(sys.argv[3]))
nodes = set(N["nodes"])
cells = {c["name"]: c for c in D["cells"]}
out = []
for n, c in sorted(R["cells"].items()):
    if ".ustate$LUT6" not in n:
        continue
    site, bel = c["attributes"]["NEXTPNR_BEL"].split("/")
    L = bel[0]
    q = "%s.%s6" % (site, L)
    lut = cells["%s.%sLUT" % (site, L)]
    ins, fb = [], 0
    for i in range(6):
        v = lut["conn"]["I%d" % i]
        if v.get("net") == q:
            fb += 1
            continue
        r = v.get("_route")
        ins.append(r["sink"] if r else ("CONST1" if v.get("const") else "CONST0"))
    if fb != 1:
        sys.exit("%s: %d feedback pins" % (n, fb))
    assert q in nodes and all(x in nodes for x in ins), n
    out.append({"cell": n, "q": q, "ins": ins})
json.dump(out, open(sys.argv[4], "w"), indent=1)
print("arbs: %d arbiters" % len(out))
for a in out:
    print(" ", a["cell"].replace("urig.udut.", ""), a["q"], len(a["ins"]))
