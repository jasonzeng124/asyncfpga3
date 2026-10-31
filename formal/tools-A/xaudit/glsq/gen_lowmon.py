#!/usr/bin/env python3
"""gen_lowmon.py -- UNTRUSTED (lead; corrected after audit P15a: the LUT5 cells drive O5, not O6): print
LOW_EDGE <t> <cell> <value> for every change of a bd_arbiter grant (ugrant$LUT5/$LUT6) and R0 (ustate$LUT5)
output, on the port the cell actually drives.   python3 -I gen_lowmon.py GLS_WORK > lowmon.v"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lutnet import load
nm, icbuf, cells, drv = load(sys.argv[1])
out = ["module lowmon;"]; n = 0
for name, c in sorted(nm.items()):
    if ".uarb" not in name or not (".ugrant$" in name or name.endswith("ustate$LUT5")): continue
    op = cells[c]["op"]
    if op is None: print(f"// {name}: no output", file=sys.stderr); continue
    tag = name.split("udut.")[-1]; n += 1
    out.append(f"  always @(tb_run.dut.{c}.{op}) $display(\"LOW_EDGE %0t {tag} %b\", $realtime, tb_run.dut.{c}.{op});")
out.append("endmodule")
print(f"// {n} outputs monitored", file=sys.stderr)
print("\n".join(out))
