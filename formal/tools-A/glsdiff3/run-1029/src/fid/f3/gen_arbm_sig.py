#!/usr/bin/env python3
"""nets.map (this route) -> arbm_sig.vh for tb_f3_arbm.v.  Usage: gen_arbm_sig.py WORKDIR"""
import os, sys
w = sys.argv[1]
nets = {}
for line in open(os.path.join(w, "nets.map")):
    if line.startswith("#"):
        continue
    v, name = line.split(None, 1)
    nets[name.strip()] = v
want = {"R1": "r1", "R2": "r2", "RING3": "ring3"}
for k in range(6):
    want["G1_%d" % k] = "ch[%d].g1c" % k
    want["G2_%d" % k] = "ch[%d].g2c" % k
    want["Q_%d" % k] = "q_dly_probe[%d]" % k
out = []
for mac, name in want.items():
    if name not in nets:
        sys.exit("gen_arbm_sig.py: net %s not in nets.map" % name)
    out.append("`define %s tb_f3_arbm.dut.%s" % (mac, nets[name]))
open(os.path.join(w, "arbm_sig.vh"), "w").write("\n".join(out) + "\n")
