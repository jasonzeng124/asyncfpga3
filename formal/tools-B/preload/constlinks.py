#!/usr/bin/env python3
"""tools-B/preload/constlinks.py NET.json ROUTED.json DUMP.json (shard B, UNTRUSTED): link instances whose latch state nodes
never move in a simx run (DUMP from `simx --dump` on an ordinary run). These are the candidates for preload_net.py:
a loop variable's entry constant (xorshift ulink_n6, collatz ulink_n7) shows up here, as do links whose data is constant
for other reasons (check the kernel Verilog before preloading one: the link must feed a loop header mux's entry input)."""
import json, re, sys, collections
N = json.load(open(sys.argv[1])); cells = json.load(open(sys.argv[2]))["modules"]["top"]["cells"]
D = json.load(open(sys.argv[3]))["nodes"]
byname = {g["name"]: g["out"] for g in N["gates"]}
pat = re.compile(r"^(.*?\.(ulink_\w+?))\.(?:many\.stage\[\d+\]\.u\.)?lat\.(?:pair\[\d+\]|odd)\.u\$LUT[56]$")
grp = collections.defaultdict(lambda: [0, 0])
for cn, c in cells.items():
    m = pat.match(cn)
    if not m: continue
    b = re.match(r"^(SLICE_X\d+Y\d+)/([A-D])([56])LUT$", c["attributes"].get("NEXTPNR_BEL", ""))
    if not b: continue
    o = byname.get("%s.%sLUT.O%s" % b.groups())
    h = D.get(str(o))
    grp[m.group(2)][0] += 1
    if h and (h[0] or h[1]): grp[m.group(2)][1] += 1
for k, (n, moving) in sorted(grp.items()):
    if moving == 0: print("%-28s %3d latch halves, none moved (value 0 throughout)" % (k, n))
