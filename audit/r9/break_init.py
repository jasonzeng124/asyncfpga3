#!/usr/bin/env python3
"""Negative control: force INIT=0 (stuck-at-0) on every urig.udut.umux*.udat.pair[0] LUT6 (data bit 0 of every mux)
in a copy of the s4_max bits-built netlist_baked.v.  usage: break_init.py ROUTED_JSON NAMES_MAP NETLIST_IN NETLIST_OUT"""
import json, re, sys
j = json.load(open(sys.argv[1])); m = list(j['modules'].values())[0]
bels = {c['attributes']['NEXTPNR_BEL']: k for k, c in m['cells'].items()
        if re.match(r'urig\.udut\.umux\d+\.udat\.pair\[0\]\.u\$LUT6$', k)}
cname = {}
for ln in open(sys.argv[2]):
    p = ln.split()
    if len(p) == 2 and p[1] in bels: cname[p[0]] = p[1]
txt = open(sys.argv[3]).read(); n = 0
def sub(mo):
    global n
    if mo.group(4) not in cname: return mo.group(0)
    n += 1; print(mo.group(4), cname[mo.group(4)], bels[cname[mo.group(4)]], mo.group(2), "-> 64'h0")
    return mo.group(1) + "64'h0000000000000000" + mo.group(3) + " " + mo.group(4)
txt = re.sub(r"(SLICE_LUTX #\(\.INIT\()(64'h[0-9a-f]+)(\)[^;]*?\)) (c_\d+)", sub, txt)
open(sys.argv[4], "w").write(txt)
print("bels", len(bels), "matched c_ names", len(cname), "replaced", n)
