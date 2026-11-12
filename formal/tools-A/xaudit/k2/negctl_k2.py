#!/usr/bin/env python3
"""negctl_k2.py -- events4/negctl.py's NEG-fb, generalised (UNTRUSTED input mutation, probe K2).

    python3 negctl_k2.py SKEL.json BANDS.json OUT.bands.json CELL [PS]

Finds CELL's own-feedback pin in the skeleton (the input pin whose net is the cell's own O,
found from the netlist, not from a pin name: nextpnr permutes LUT pins per route, so gcd's
hard-coded "/I0" is not the feedback pin on another route) and adds PS (default 1500) ps to
both ends of that arc's band.  The checker must then report that stage's Back pins with
margin <= 0 (a residual item), or the negative control has failed."""
import json
import sys

skel, src, out, cell = sys.argv[1:5]
ps = int(sys.argv[5]) if len(sys.argv) > 5 else 1500
m = json.load(open(skel))["modules"]
c = next(iter(m.values()))["cells"][cell]
o = c["connections"]["O"][0]
pins = [p for p, v in c["connections"].items() if c["port_directions"][p] == "input" and v == [o]]
if len(pins) != 1:
    sys.exit(f"negctl_k2: {cell}: own-feedback pins {pins}, expected exactly one")
k = f"{cell}/{pins[0]}"
b = json.load(open(src))
lo, hi = b["arcs"][k]
b["arcs"][k] = [lo + ps, hi + ps]
print(f"negctl_k2 fb: {k} {lo},{hi} -> {lo + ps},{hi + ps}")
json.dump(b, open(out, "w"))
