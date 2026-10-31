#!/usr/bin/env python3
"""gen_lowmon.py -- UNTRUSTED (lead, 2026-10-31): monitor for ArbEdge's quiet start on the research GLS:
print LOW_EDGE <t> <cell> <pin> <value> for every change of a bd_arbiter grant (ugrant$LUT5/$LUT6 -> O6 of the
physical cells, i.e. g1/g2) and of ustate$LUT5 (R0), so the analysis can check they stay low until T0.
    python3 -I gen_lowmon.py GLS_WORK > lowmon.v"""
import re, sys, os
W = sys.argv[1]
names = {}
for ln in open(os.path.join(W, "names.map")):
    p = ln.split()
    if len(p) == 2 and (".ugrant$" in p[1] or p[1].endswith("ustate$LUT5")) and ".uarb" in p[1]: names[p[0]] = p[1]
net = open(os.path.join(W, "netlist_baked.v")).read()
out = ["module lowmon;"]
for c, nm in sorted(names.items()):
    m = re.search(r"SLICE_LUTX #\([^;]*?\) " + c + r" \(([^;]*)\);", net)
    if not m: print(f"// {c} {nm}: not found", file=sys.stderr); continue
    tag = nm.split("udut.")[-1]
    out.append(f"  always @(tb_run.dut.{c}.O6) $display(\"LOW_EDGE %0t {tag} %b\", $realtime, tb_run.dut.{c}.O6);")
out.append("endmodule")
print("\n".join(out))
