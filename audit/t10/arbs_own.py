#!/usr/bin/env python3
"""arbs_own.py (audit T10): the Lean arbiter list (NetPS All.lean `arbs`) vs the auditor's decode and rebuild.
For each entry: q's gate is a bd_arbiter ustate LUT6 in nextpnr's routed JSON; `ins` = that gate's pin nodes minus the
one pin whose route traces back to q (the state feedback). Also: the design has exactly that many ustate cells.
    python3 -I arbs_own.py LEANDIR NET.json ROUTED.json"""
import json, re, os, sys
d, netp, routp = sys.argv[1:4]
names = []
for m in re.finditer(r'def n\d+ : List String := \[(.*?)\]\n', open(os.path.join(d, "Nodes.lean")).read(), re.S):
    names += json.loads("[" + m.group(1) + "]")
s = open(d + "/All.lean").read(); a = s[s.index("def arbs"):s.index("def boundary")]
arbs = [(int(q), [int(x) for x in re.findall(r"\d+", ins)]) for q, ins in re.findall(r"⟨(\d+), \[([^\]]*)\]⟩", a)]
N = json.load(open(netp)); nn = N["nodes"]; drv = {g["out"]: g for g in N["gates"]}; idx = {n: i for i, n in enumerate(nn)}
R = json.load(open(routp))["modules"]["top"]
bel = {c["attributes"].get("NEXTPNR_BEL"): cn for cn, c in R["cells"].items()}
ust = {cn.split(".ustate")[0] for cn in R["cells"] if ".ustate" in cn}
def src(n):
    while True:
        g = drv.get(n)
        if g is None or g["kind"] not in ("pip", "hop"):
            return n
        n = g["ins"][0]
ok = 0
for q, ins in arbs:
    nq = names[q]; site, L = nq.split(".")[0], nq.split(".")[1][0]
    cn = bel.get("%s/%s6LUT" % (site, L), "")
    g = drv[idx[nq]]
    fb = [p for p in g["ins"] if src(p) == idx[nq]]
    other = sorted(nn[p] for p in g["ins"] if src(p) != idx[nq])
    good = ".ustate" in cn and len(fb) == 1 and other == sorted(names[i] for i in ins)
    ok += good
    print(nq, cn.split(".ustate")[0], "feedback pins", len(fb), "ins = the other 5 pins:", good)
print("ARBS %d of %d entries OK; ustate cells in the design: %d" % (ok, len(arbs), len(ust)))
