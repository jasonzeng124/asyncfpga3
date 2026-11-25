#!/usr/bin/env python3
"""tools-B/auto/bnd_const.py BND.json NET.json (shard B, UNTRUSTED): replace "const0" in the boundary's out0_data by a decoded
node with no driving gate that is constant 0 in simx (an interconnect GND_WIRE), so simx_conv.py can read a kernel whose
result has constant bits (isprime: out0_data[31:1] = 0). const1 is refused (a VCC_WIRE has no driver in the decoded net,
so simx would hold it at 0)."""
import json, sys
bf, nf = sys.argv[1:3]
BJ = json.load(open(bf)); N = json.load(open(nf))
drv = set(g["out"] for g in N["gates"]); names = N["nodes"]
gnd = next(n for i, n in enumerate(names) if n.endswith("/GND_WIRE") and i not in drv)
B = BJ["boundary"]; k = 0
for key, v in B.items():
    if isinstance(v, list):
        if "const1" in v: sys.exit("bnd_const: %s has const1 bits (not handled)" % key)
        k += v.count("const0"); B[key] = [gnd if x == "const0" else x for x in v]
    elif v == "const1": sys.exit("bnd_const: %s is const1" % key)
    elif v == "const0": B[key] = gnd; k += 1
json.dump(BJ, open(bf, "w"))
print("bnd_const: %d const0 boundary bits -> %s (no driver)" % (k, gnd))
