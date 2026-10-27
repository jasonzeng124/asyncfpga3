#!/usr/bin/env python3
"""Trim the large build outputs of one route to the fixture files gen3.py needs
(probe C-11f):  trim.py SEED   (reads build/, writes fixture/*.xz)
  gcd_hw_<s>.synth.json  the yosys netlist nextpnr read: non-blackbox modules only;
                         per cell type, parameters, connections and the `src` attribute
  gcd_hw_<s>.hint.json   nextpnr's placement: per cell its type and NEXTPNR_BEL only
  gcd_hw_<s>.fromBit.fasm, gcd_hw_<s>.fasm, gcd_hw_<s>.xdc   copied
"""
import json, lzma, os, shutil, sys
HERE = os.path.dirname(os.path.abspath(__file__))
s = sys.argv[1]
B, F = os.path.join(HERE, "build"), os.path.join(HERE, "fixture")
d = json.load(open(os.path.join(B, "gcd_hw_%s.json" % s)))
mods = {}
for n, m in d["modules"].items():
    if m.get("attributes", {}).get("blackbox") or not m.get("cells"):
        continue
    mods[n] = {"attributes": {k: v for k, v in m.get("attributes", {}).items() if k == "top"},
               "ports": m["ports"],
               "cells": {cn: {"type": c["type"], "parameters": c.get("parameters", {}),
                              "connections": c["connections"],
                              "attributes": {k: v for k, v in c.get("attributes", {}).items() if k == "src"}}
                         for cn, c in m["cells"].items()}}
w = lambda name, obj: lzma.open(os.path.join(F, name + ".xz"), "wt").write(json.dumps(obj))  # key order kept: gen3 output depends on it
w("gcd_hw_%s.synth.json" % s, {"modules": mods})
r = list(json.load(open(os.path.join(B, "gcd_hw_%s.routed.json" % s)))["modules"].values())[0]
w("gcd_hw_%s.hint.json" % s, {"modules": {"top": {"cells": {
    n: {"type": c["type"], "attributes": {"NEXTPNR_BEL": c.get("attributes", {}).get("NEXTPNR_BEL", "")}}
    for n, c in r["cells"].items()}}}})
for x in ("fromBit.fasm", "fasm"):
    with open(os.path.join(B, "gcd_hw_%s.%s" % (s, x)), "rb") as fi, lzma.open(os.path.join(F, "gcd_hw_%s.%s.xz" % (s, x)), "wb") as fo:
        shutil.copyfileobj(fi, fo)
shutil.copy(os.path.join(B, "gcd_hw_%s.xdc" % s), os.path.join(F, "gcd_hw_%s.xdc" % s))
print("trim: fixture/gcd_hw_%s.* written" % s)
