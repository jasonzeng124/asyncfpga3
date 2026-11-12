#!/usr/bin/env python3
"""Negative controls for check.sh (probe C-11c): a defect injected into the
BITS (the FASM read back from the .bit), never into Lean.

    python3 mutate2.py KIND IN.fasm IN.json BELS OUT.fasm

IN.json is fasm2lean2's extraction of IN.fasm (pins, sources, pips); BELS the
placement hint, used here only to pick a target LUT by cell name.

KIND
  init   flip one INIT bit of the arbiter's ugrant LUT6_2 (the one LUT without
         (* keep *)): the lowest address consistent with its tied pins that
         has A6 = 1, so it changes O6 (= g2) on a live input
  pips   re-point the INT IMUX pip feeding one live pin of that LUT to another
         legal source of the same IMUX wire that carries a DIFFERENT net of the
         design (a mis-route that every other check would still accept)
  short  add a second active driver onto that IMUX wire (must be refused)
  ff     add a slice flip-flop feature in the ugrant site (must be refused)
  carry  add a CARRY4 feature in the ugrant site (must be refused)
"""
import importlib.util
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("f2l", os.path.join(HERE, "fasm2lean2.py"))
f2l = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f2l)

kind, src, js, bels, dst = sys.argv[1:]
L = open(src).read().split("\n")
orig = list(L)
res = json.load(open(js))
hint = {}
for line in open(bels):
    c, o, site, letter = line.split()
    hint[(c, o)] = (site, letter)
site, letter = hint[("arb.ugrant", "O6")]
li = [i for i, l in enumerate(res["luts"]) if (l["site"], l["lut"]) == (site, letter)][0]
lut = res["luts"][li]
pre = "%s.%s.%sLUT" % (lut["tile"], lut["slice"], lut["lut"])


if kind == "init":
    fixed = {k: (p["src"]["v"]) for k, p in enumerate(lut["pins"]) if p["src"]["k"] == "const"}
    assert fixed.get(5) is True, "ugrant's A6 is not tied high"
    addr = min(a for a in range(64) if all(((a >> k) & 1) == v for k, v in fixed.items()))
    for i, l in enumerate(L):
        if l.startswith(pre + ".INIT["):
            v = int(l.rsplit("'b", 1)[1], 2) ^ (1 << addr)
            L[i] = pre + ".INIT[63:0] = 64'b" + format(v, "064b")
    print("mutate2: %s INIT bit %d flipped" % (pre, addr), file=sys.stderr)
elif kind in ("pips", "short"):
    fab = f2l.Fabric()
    feats, vecs = f2l.read_fasm(src)
    ex = f2l.Extract(fab, feats, vecs, {})
    found = None
    for p in lut["pins"]:                       # live pins in A1..A6 order
        if p["src"]["k"] == "const":
            continue
        qs = [q for q in p["pips"] if q["tile"].startswith("INT_") and q["dst"].startswith("IMUX")
              and not q["pseudo"]]
        if not qs:
            continue
        q = qs[0]
        tile = q["tile"]
        j = fab.tt(fab.ttype(tile))
        mine = ex.walk(tile, q["src"], "probe")[0]
        for alt in sorted(pp["src_wire"] for pp in j["_by_dst"][q["dst"]]):
            if alt == q["src"]:
                continue
            n = fab.node(tile, alt)
            if not ex.is_driven(n):
                continue
            try:                                # carries a SIGNAL net of the design
                s2, _ = ex.walk(tile, alt, "probe")
            except SystemExit:
                continue
            if s2[0] == "const" or s2[1:] == mine[1:]:
                continue
            found = (p, q, alt)
            break
        if found:
            break
    if not found:
        sys.exit("mutate2: no live pin of %s has an alternative signal source" % pre)
    p, q, alt = found
    old = "%s.%s.%s" % (q["tile"], q["dst"], q["src"])
    new = "%s.%s.%s" % (q["tile"], q["dst"], alt)
    assert old in [x.strip() for x in L], old
    if kind == "pips":
        L = [new if l.strip() == old else l for l in L]
        print("mutate2: pin %s (was %s): %s -> %s" % (p["pin"], p["src"], old, new), file=sys.stderr)
    else:
        L.append(new)
        print("mutate2: added %s next to %s" % (new, old), file=sys.stderr)
elif kind == "ff":
    L.append("%s.%s.%sFF.ZINI" % (lut["tile"], lut["slice"], lut["lut"]))
elif kind == "carry":
    L.append("%s.%s.CARRY4.%sCY0" % (lut["tile"], lut["slice"], lut["lut"]))
else:
    sys.exit("unknown kind " + kind)
if L == orig:
    sys.exit("mutation %s did not apply" % kind)
open(dst, "w").write("\n".join(L) + "\n")
