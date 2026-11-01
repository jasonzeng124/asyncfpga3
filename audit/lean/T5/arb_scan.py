#!/usr/bin/env python3
"""Audit T5: list every cell of the routed design that belongs to an arbiter, by hierarchy name and type,
independent of shard A's arbs.py. usage: python3 -I arb_scan.py routed.json"""
import json, sys, re, collections
R = json.load(open(sys.argv[1]))["modules"]["top"]
cells = R["cells"]
types = collections.Counter(c["type"] for c in cells.values())
print("cell types:", dict(types))
arb = {n: c for n, c in cells.items() if re.search(r"arb", n, re.I)}
print("cells with 'arb' in name:", len(arb))
inst = collections.defaultdict(list)
for n, c in sorted(arb.items()):
    m = re.match(r"(.*\.u?arb\w*)\.(.*)", n)
    key = m.group(1) if m else n
    inst[key].append((n[len(key):], c["type"], c["attributes"].get("NEXTPNR_BEL")))
for k, v in sorted(inst.items()):
    print(k)
    for x in v: print("   ", x)
# every LUT cell whose name says ustate
print("ustate cells:", sorted(n for n in cells if "ustate" in n))
# hdlname / module type attributes mentioning bd_arbiter
mods = collections.Counter()
for n, c in cells.items():
    for a, v in c["attributes"].items():
        if isinstance(v, str) and "bd_arb" in v:
            mods[(a, v[:80])] += 1
print("attributes mentioning bd_arb:", mods.most_common(20))
