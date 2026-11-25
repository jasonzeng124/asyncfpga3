#!/usr/bin/env python3
"""Negative controls for check.sh: a defect injected into the BITS (FASM
features of seed 1's FASM read back from the .bit), never into Lean.

    python3 mutate.py KIND IN.fasm OUT.fasm

KIND
  init   clear INIT bit 13 of the q1 LUT (CLBLM_R_X29Y95 BLUT; physical
         address B1=q=1, B2=rst=0, B3=b=1, B4=a=1: the "both high, hold 1" entry)
  pips   re-point two INT pips so pins B3/B2 of that LUT swap rst and b
         (IMUX17 <- SS2END0, IMUX18 <- WW2END0; both are legal pips)
  short  add a second active driver onto IMUX17's node (fasm2lean must refuse)
"""
import sys

kind, src, dst = sys.argv[1:]
L = open(src).read().split("\n")
orig = list(L)
if kind == "init":
    for i, l in enumerate(L):
        if l.startswith("CLBLM_R_X29Y95.SLICEM_X0.BLUT.INIT["):
            v = int(l.rsplit("'b", 1)[1], 2)
            assert v >> 13 & 1, "bit 13 already clear"
            L[i] = "CLBLM_R_X29Y95.SLICEM_X0.BLUT.INIT[63:0] = 64'b" + format(v & ~(1 << 13), "064b")
elif kind == "pips":
    sw = {"INT_R_X29Y95.IMUX17.WW2END0": "INT_R_X29Y95.IMUX17.SS2END0",
          "INT_R_X29Y95.IMUX18.SS2END0": "INT_R_X29Y95.IMUX18.WW2END0"}
    L = [sw.get(l.strip(), l) for l in L]
elif kind == "short":
    L.append("INT_R_X29Y95.IMUX17.SS2END0")
else:
    sys.exit("unknown kind " + kind)
if L == orig:
    sys.exit("mutation %s did not apply" % kind)
open(dst, "w").write("\n".join(L) + "\n")
