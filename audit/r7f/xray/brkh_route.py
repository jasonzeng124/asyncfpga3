"""Auditor: count routed nets whose ROUTING attribute uses a BRKH_INT inverted pip."""
import json, sys, re
INV = re.compile(r"BRKH_INT_(NL1BEG[0-2]|NR1BEG[0-3]|SL1END[0-3]|SR1END[1-3])")
top = json.load(open(sys.argv[1]))["modules"]["top"]
n = 0; uses = 0
for name, nn in top["netnames"].items():
    r = nn.get("attributes", {}).get("ROUTING", "")
    k = sum(1 for p in r.split(";") if "BRKH_INT" in p and INV.search(p) and "->" in p)
    if k: n += 1; uses += k
print(sys.argv[1], "nets through inverted BRKH_INT pips:", n, "pip uses:", uses)
