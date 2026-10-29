#!/usr/bin/env python3
"""Map the rig's 32-bit result bus (gcd_rig out0_data == gcd_hw rig_res_data) to netlist wires via nets.map."""
import sys, os
work = sys.argv[1]
by = {}
for line in open(os.path.join(work, "nets.map")):
    if line.startswith("#"): continue
    w, _, n = line.strip().partition(" ")
    by.setdefault(n, []).append(w)
out = []
for cand in ("urig.out0_data[%d]", "rig_res_data[%d]", "urig.res_data[%d]"):
    ws = [by.get(cand % i) for i in range(32)]
    if all(ws):
        out.append(f"// result bus from nets.map name {cand}")
        for i in range(32):
            out.append(f"`define R22D{i} tb_run.dut.{ws[i][0]}")
        break
else:
    sys.exit("result bus not found in nets.map")
open(os.path.join(work, "r22sig.vh"), "w").write("\n".join(out) + "\n")
print("\n".join(out[:3]))
