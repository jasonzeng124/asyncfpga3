#!/usr/bin/env python3
"""Trim the large build outputs of one route to the fixture files gen3.py needs
(probe C-11f):  trim.py SEED   (reads build/, writes fixture/*.xz)
             trim.py --kernel K SEED   (C-11g: reads build/k_K/sSEED/K.*, writes fixture/K_SEED.*)
  gcd_hw_<s>.synth.json  the yosys netlist nextpnr read: non-blackbox modules only;
                         per cell type, parameters, connections and the `src` attribute
  gcd_hw_<s>.hint.json   nextpnr's placement: per cell its type and NEXTPNR_BEL only
  gcd_hw_<s>.fromBit.fasm, gcd_hw_<s>.fasm, gcd_hw_<s>.xdc   copied
"""
import json, lzma, os, shutil, sys
HERE = os.path.dirname(os.path.abspath(__file__))
B, F = os.path.join(HERE, "build"), os.path.join(HERE, "fixture")
if sys.argv[1] == "--kernel":
    k, s0 = sys.argv[2], sys.argv[3]
    B, s, PFX = os.path.join(B, "k_" + k, "s" + s0), s0, k
    bname = lambda x: os.path.join(B, "%s.%s" % (k, x))
else:
    s, PFX = sys.argv[1], "gcd_hw"
    bname = lambda x: os.path.join(B, "gcd_hw_%s.%s" % (s, x))
d = json.load(open(bname("json")))
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
w("%s_%s.synth.json" % (PFX, s), {"modules": mods})
r = list(json.load(open(bname("routed.json")))["modules"].values())[0]
w("%s_%s.hint.json" % (PFX, s), {"modules": {"top": {"cells": {
    n: {"type": c["type"], "attributes": {"NEXTPNR_BEL": c.get("attributes", {}).get("NEXTPNR_BEL", "")}}
    for n, c in r["cells"].items()}}}})
for x in ("fromBit.fasm", "fasm"):
    with open(bname(x), "rb") as fi, lzma.open(os.path.join(F, "%s_%s.%s.xz" % (PFX, s, x)), "wb") as fo:
        shutil.copyfileobj(fi, fo)
shutil.copy(bname("xdc"), os.path.join(F, "%s_%s.xdc" % (PFX, s)))
print("trim: fixture/%s_%s.* written" % (PFX, s))
