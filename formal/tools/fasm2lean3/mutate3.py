#!/usr/bin/env python3
"""Negative controls (probe C-11f): a defect injected into the BITS (the FASM read back
from the .bit), never into Lean.

    python3 mutate3.py KIND IN.fasm PHYS.json SITE OUT.fasm

PHYS.json is fasm2lean3's extraction of IN.fasm; SITE a physical LUT site
("SLICE_X0Y63.ALUT"). KIND:
  init   flip the INIT bit of SITE at the lowest address consistent with its tied pins
  pips   re-point the INT IMUX pip feeding one live pin of SITE to another legal source
         of the same IMUX wire that carries a DIFFERENT signal (a mis-route)
  ffinit flip ZINI of the first used FF of SITE's slice (power-up value)
  clkinv add CLKINV to SITE's slice (if it has an FF)
"""
import importlib.util
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("f3", os.path.join(HERE, "fasm2lean3.py"))
f3 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f3)
F2 = f3.F2

kind, src, js, site, dst = sys.argv[1:]
L = open(src).read().split("\n")
orig = list(L)
P = json.load(open(js))
cell = [c for c in P["cells"] if c["name"] == site][0]
fab = f3.Fabric3()
# tile.slice prefix of SITE
sn, letter = site.split(".")[0], site.split(".")[1][0]
tile = [t for t, g in fab.grid.items() if sn in g.get("sites", {})][0]
j = fab.tt(fab.ttype(tile))
st = [s for s in j["sites"] if fab.site_name(tile, s) == sn][0]
pre = "%s.%s_X%d" % (tile, st["type"], st["x_coord"])

if kind == "init":
    fixed = {k: cell["conn"]["I%d" % k]["const"] for k in range(6) if "const" in cell["conn"]["I%d" % k]}
    addr = min(a for a in range(64) if all(((a >> k) & 1) == v for k, v in fixed.items()))
    name = "%s.%sLUT.INIT" % (pre, letter)
    v = cell["init"] ^ (1 << addr)
    L = [l for l in L if not l.startswith(name + "[")]
    L.append(name + "[63:0] = 64'b" + format(v, "064b"))
    print("mutate3: %s INIT bit %d flipped" % (name, addr), file=sys.stderr)
elif kind == "pips":
    feats, vecs = f3.read_fasm3(src)
    ex = f3.Extract3(fab, feats, vecs, {})
    found = None
    for k in range(1, 7):
        if "const" in cell["conn"]["I%d" % (k - 1)]:
            continue
        pin = st["site_pins"]["%s%d" % (letter, k)]
        s0, path = ex.walk(tile, pin["wire"], "probe")
        qs = [(t, p) for t, p, ps, _n in path if t.startswith("INT_") and p["dst_wire"].startswith("IMUX") and not ps]
        if not qs:
            continue
        t, q = qs[0]
        jt = fab.tt(fab.ttype(t))
        for alt in sorted(pp["src_wire"] for pp in jt["_by_dst"][q["dst_wire"]]):
            if alt == q["src_wire"]:
                continue
            if not ex.is_driven(fab.node(t, alt)):
                continue
            try:
                s2, _ = ex.walk(t, alt, "probe")
            except SystemExit:
                continue
            if s2[0] in ("const", "float") or s2[1:] == s0[1:]:
                continue
            found = (k, t, q, alt)
            break
        if found:
            break
    if not found:
        sys.exit("mutate3: no live pin of %s has an alternative signal source" % site)
    k, t, q, alt = found
    old = "%s.%s.%s" % (t, q["dst_wire"], q["src_wire"])
    new = "%s.%s.%s" % (t, q["dst_wire"], alt)
    assert old in [x.strip() for x in L], old
    L = [new if l.strip() == old else l for l in L]
    print("mutate3: pin %s%d: %s -> %s" % (letter, k, old, new), file=sys.stderr)
elif kind == "ffinit":
    ffs = sorted(l.strip() for l in L if re.match(re.escape(pre) + r"\.[A-D]5?FFMUX\.", l.strip()))
    if not ffs:
        sys.exit("mutate3: no FF in %s" % pre)
    ff = ffs[0].split(".")[2].replace("MUX", "")
    z = "%s.%s.ZINI" % (pre, ff)
    L = [l for l in L if l.strip() != z] if z in [x.strip() for x in L] else L + [z]
    print("mutate3: toggled %s" % z, file=sys.stderr)
elif kind == "clkinv":
    L = [l for l in L if l.strip() != pre + ".NOCLKINV"] + [pre + ".CLKINV"]
    print("mutate3: %s.CLKINV" % pre, file=sys.stderr)
else:
    sys.exit("unknown kind " + kind)
if L == orig:
    sys.exit("mutation %s did not apply" % kind)
open(dst, "w").write("\n".join(L) + "\n")
