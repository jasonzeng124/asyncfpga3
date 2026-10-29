#!/usr/bin/env python3
"""Auditor r17 causal back-trace (non-X) on the full VCD: for an edge on NET at T, the driver cell's input whose
last edge (on the post-ICBUF w-net) lies closest before T - (pin arc) is the cause; recurse into its ICBUF source.
usage: ctrace.py WORK VCD NET T [MAXSTEPS]  (pin arcs: the cell's T<pin><out> parameter, prims.v default if absent)"""
import sys, re, bisect, collections
exec(open(__file__.replace("ctrace.py", "xtrace.py")).read().split("n, t = NET, T")[0].replace(
    "W, VCD, NET, T = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])",
    "W, VCD, NET, T = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])"))
MAXS = int(sys.argv[5]) if len(sys.argv) > 5 else 200
site = {}
import json
for nm, c in json.load(open(W + "/routed.json"))["modules"]["top"]["cells"].items():
    site[nm] = c.get("attributes", {}).get("NEXTPNR_BEL", "")
def reg(cell):
    m = re.match(r"^[A-Z0-9_]*?_X(\d+)Y(\d+)/", site.get(names.get(cell, cell), ""))
    return (int(m.group(1)) // 10, int(m.group(2)) // 10) if m else None
n, t = NET, T
for step in range(MAXS):
    if n not in drv: print("END no driver", n, t); break
    cell, port = drv[n]; typ, pd, cd = cells[cell]
    best = None
    for p, w in cd.items():
        if p in OUTS.get(typ, ()) or not w.startswith(("w", "n")): continue
        arc = int(pd.get("T%s%s" % (p, port), 1 if typ == "SLICE_FFX" else 0))
        tt = tim.get(w, []); i = bisect.bisect_right(tt, t - arc)
        if i == 0: continue
        te = tt[i - 1]; slack = t - arc - te
        if best is None or slack < best[0]: best = (slack, p, w, te, arc, ev[w][i - 1][1])
    if typ == "SLICE_FFX":   # a flop output edge is caused by its clock edge
        w = cd["CK"]; tt = tim.get(w, []); i = bisect.bisect_right(tt, t - 1)
        best = (0, "CK", w, tt[i-1], int(pd.get("TCKQ", 0)), ev[w][i-1][1]) if i else best
    if best is None: print("END no input edge", n, t); break
    slack, p, w, te, arc, v = best
    src, D = icb.get(w, (w, 0))
    print(f"{t:>8} {n:7s}={val(n,t)} {netname.get(n,'')[:58]:58s} <- {typ:10s} {names.get(cell,cell)[:70]:70s} r{reg(cell)} "
          f"pin {p}={v}@{te} arc {arc} slack {slack} | wire {D} from {src}")
    n, t = src, te - D
