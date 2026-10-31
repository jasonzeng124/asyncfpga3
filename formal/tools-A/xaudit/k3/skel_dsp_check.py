#!/usr/bin/env python3
"""Probe K3: does the control skeleton read any net that routed2x_k3.py --cut-type made a free
input (ipow's DSP48E1 outputs)?   skel_dsp_check.py NET.json SKEL.json  -> exit 1 if it does.

Soundness does not depend on the answer (skel.py turns every net a kept LUT reads but the
skeleton does not drive into a free input, so a verdict holds for every waveform on it), but if
a control node read a DSP output, the DSP's timing would sit inside a select's bundling
(SelOK) with no band at all.  Prints each skeleton input port and where its net comes from."""
import json, sys
n = json.load(open(sys.argv[1]))["modules"]["gcd_ctl"]
s = json.load(open(sys.argv[2]))["modules"]["gcd_ctl"]
names = {}
for nm, v in n["netnames"].items():
    for b in v["bits"]:
        names.setdefault(b, []).append(nm)
free = {b for p, v in n["ports"].items() if v["direction"] == "input" for b in v["bits"]}
bad = 0
for p, v in sorted(s["ports"].items()):
    b = v["bits"][0]
    f = b in free and p != "rig_rst"
    bad += f
    print(f"{p:14s} {','.join(names.get(b, ['?'])[:2]):40s} {'NETLIST FREE INPUT (cut cell output)' if f else ''}")
print(f"skeleton inputs {len(s['ports'])}, of them netlist free inputs other than rig_rst: {bad}")
sys.exit(1 if bad else 0)
