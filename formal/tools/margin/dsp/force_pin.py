#!/usr/bin/env python3
"""margin/dsp/force_pin.py (shard C, UNTRUSTED): tie one decoded cell pin to a constant (a what-if on the decoded net).

    python3 force_pin.py D0.json CELL PIN 0|1 OUT.json

CELL / PIN as in decode_base's d0 (e.g. SLICE_X19Y65.F7A S). The pin's walked route is dropped and the pin reads
CONST0 / CONST1; the route's pips stay in the net as untraced active pips (build_net adds them; nothing reads them
through this pin any more). The cell gets "forced": [PIN, old source] so the what-if is visible in the output.
Used for route 19's F7AMUX select (decoded from the bits: VCC through default pips; nextpnr's json: GND).
"""
import json, sys

d0, cell, pin, v, out = sys.argv[1:6]
D = json.load(open(d0))
c = [x for x in D["cells"] if x["name"] == cell]
if len(c) != 1 or pin not in c[0]["conn"]:
    sys.exit("force_pin: %s %s not in %s" % (cell, pin, d0))
c = c[0]
old = c["conn"][pin]
c["conn"][pin] = {"const": v == "1"}
c.setdefault("forced", []).append([pin, {k: x for k, x in old.items() if k != "_route"},
                                   [p[:3] for p in old.get("_route", {}).get("pips", [])]])
json.dump(D, open(out, "w"), indent=0, sort_keys=True)
print("force_pin: %s %s: was %s (route %s) -> const %s" % (cell, pin, {k: x for k, x in old.items() if k != "_route"},
      [".".join(map(str, p[:3])) for p in old.get("_route", {}).get("pips", [])], v), file=sys.stderr)
