#!/usr/bin/env python3
"""tools-B/auto/lutreaders.py ROUTED.json NAME... (shard B): for each yosys LUT cell name (or prefix; nextpnr's $LUT6 /
$LUT5 halves included), the routed cells that read its output. Used to tell a mux's decode LUTs (read by the joins
.uj<k>.u) from its data LUTs (read by latches / registers downstream)."""
import json, sys, collections
C = json.load(open(sys.argv[1]))["modules"]["top"]["cells"]
drv = {}
for cn, c in C.items():
    for p, d in c["port_directions"].items():
        if d == "output":
            for b in c["connections"][p]: drv[b] = cn
rd = collections.defaultdict(set)
for cn, c in C.items():
    for p, d in c["port_directions"].items():
        if d == "input":
            for b in c["connections"][p]:
                if b in drv: rd[drv[b]].add(cn)
for n in sys.argv[2:]:
    r = set()
    for cn in C:
        if cn == n or cn.startswith(n + "$"): r |= rd.get(cn, set())
    print(n.split(".")[-1][-14:], "->", sorted(x.replace("bridge_i.udut.", "")[:60] for x in r)[:4])
