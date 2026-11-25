#!/usr/bin/env python3
"""tools-B/preload/inject_carry.py NET.json SLICE PS OUT.json: a simx classes file whose "I" list adds PS ps to the
carry-in arc (pin 0) of every CARRY4 output gate of SLICE (e.g. SLICE_X22Y54): a defect in one carry chain's high part,
OUTSIDE the prjxray band (a negative control, not a Spec behaviour)."""
import json, sys
N = json.load(open(sys.argv[1])); sl, ps = sys.argv[2], int(sys.argv[3])
I = [[N["nodes"][g["out"]], 0, ps] for g in N["gates"] if g["name"].startswith(sl + ".CARRY4.") and g["kind"] == "carry"]
if len(I) != 8: sys.exit("inject_carry: %s has %d CARRY4 output gates, want 8" % (sl, len(I)))
json.dump({"S": [], "F": [], "I": I}, open(sys.argv[4], "w"))
