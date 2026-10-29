#!/usr/bin/env python3
"""ev8: corrected band file = the formal band file with every LUT->LUT arc driven by a LUT O5 output
(?5LUT bel, leaves through ?MUX) replaced by my xrc arc (which charges the prjxray ROUTING_BEL
x5lut -> xMUX delay that the formal bands omit).  Everything else unchanged.
    python3 corrband.py BUILD_DIR NET.json BANDS_IN CORNER BANDS_OUT --lv2"""
import os, re, sys, json, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import entry  # noqa
xrc = entry.xrc
bd, netf, bin_, corner, bout = [a for a in sys.argv[1:] if not a.startswith("--")]
R = xrc.Route(bd); C = R.cells
N = list(json.load(open(netf))["modules"].values())[0]
B = json.load(open(bin_))
drv = {}
for cn, c in N["cells"].items():
    for p, d in c["port_directions"].items():
        if d == "output":
            for b in c["connections"][p]:
                drv[b] = cn
nch = nskip = 0
for dst, c in N["cells"].items():
    for p, bb in c["connections"].items():
        if c["port_directions"][p] != "input" or not bb or bb[0] not in drv:
            continue
        src = drv[bb[0]]
        if src not in C or not C[src]["attributes"].get("NEXTPNR_BEL", "").endswith("5LUT"):
            continue
        key = f"{dst}/{p}"
        if key not in B["arcs"]:
            continue
        ok = dst in C and C[dst]["type"] == "SLICE_LUTX"
        rp = [q for q in C[dst]["connections"] if re.fullmatch(r"A[1-6]", q) and (C[dst]["connections"][q] or [None])[0] is not None
              and R.driver.get(C[dst]["connections"][q][0], (None,))[0] == src] if ok else []
        s = R.sink_of_cellpin(dst, rp[0])[1] if len(rp) == 1 else None
        if s is None:
            nskip += 1; continue
        lo, hi = entry.band(s["d"], corner)
        B["arcs"][key] = [max(1, math.floor(lo)), math.ceil(hi)]
        nch += 1
B["comment"] = B.get("comment", "") + f" | ev8 auditor: {nch} O5-driven LUT arcs replaced by xrc (lv2) values incl. x5lut->xMUX; {nskip} O5 arcs not matched (kept)"
json.dump(B, open(bout, "w"))
print(corner, "replaced", nch, "kept", nskip)
