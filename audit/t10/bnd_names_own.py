#!/usr/bin/env python3
"""bnd_names_own.py (audit T10): formal's gcd_ps boundary (bnd.json, A's boundary_ps.py) bit by bit against the RTL
register / port names in MY rebuild's routed JSON: a_data[i] must be driven by bridge_i.a_data_reg[i]'s flop, b_data[i]
by b_data_reg[i]'s, out0_data[i] by the LUT driving bridge_i.o_data_pl[i] (or an alias), rst by ctrl_rst, req by req_core.
    python3 -I bnd_names_own.py BND.json ROUTED.json"""
import json, re, sys
B = json.load(open(sys.argv[1]))["boundary"]
R = json.load(open(sys.argv[2]))["modules"]["top"]
drv = {}
for cn, c in R["cells"].items():
    for p, d in c["port_directions"].items():
        if d == "output":
            for b in c["connections"].get(p, []):
                drv[b] = (c, p)
def node_of(bit):
    c, p = drv[bit]; bel = c["attributes"]["NEXTPNR_BEL"]; site, be = bel.split("/")
    if c["type"] == "SLICE_FFX":
        return "%s.%s" % (site, be[0] + ("5Q" if be[1] == "5" else "Q"))
    if c["type"] == "SLICE_LUTX":
        return "%s.%s%s" % (site, be[0], be[1])
    return "%s:%s" % (c["type"], bel)
byname = {}
for n, v in R["netnames"].items():
    byname[n] = v["bits"]
def want(name):
    b = byname.get(name)
    return node_of(b[0]) if b else None
bad = 0; tot = 0
for key, pat in (("a_data", "bridge_i.a_data_reg[%d]"), ("b_data", "bridge_i.b_data_reg[%d]")):
    for i in range(32):
        w = want(pat % i); tot += 1
        if w != B[key][i]: bad += 1; print("DIFF", key, i, B[key][i], w)
# out0 data: the kernel's out0_data port bits; try a few alias spellings
for i in range(32):
    w = None
    for pat in ("bridge_i.o_data_pl[%d]", "bridge_i.udut.out0_data[%d]", "bridge_i.o_data_capture_D[%d]"):
        w = want(pat % i)
        if w: break
    tot += 1
    if w != B["out0_data"][i]: bad += 1; print("DIFF out0_data", i, B["out0_data"][i], w)
for key, names in (("rst", ["bridge_i.ctrl_rst", "bridge_i.rst_pl"]), ("req", ["bridge_i.req_core", "bridge_i.p_end_req", "bridge_i.i_req_pl"])):
    ws = {nm: want(nm) for nm in names}; tot += 1
    hit = [nm for nm, w in ws.items() if w == B[key]]
    print(key, B[key], "named", hit or ws)
    if not hit: bad += 1
print("BOUNDARY-NAMES checked %d, differing %d" % (tot, bad))
