# region.py -- nextpnr-xilinx --pre-place script: confine a set of cells to a rectangle (build_bench.sh BD_REGION_RX).
#
# The cells whose names match BD_REGION_RX (a regex; e.g. the instances on a loop's critical cycle, from the timed event
# graph) are constrained to one rectangular region.  Its box: the bounding box those cells had on a previous route
# (BD_REGION_FROM, a routed JSON), shrunk about its centre by BD_REGION_SHRINK (default 0.6, per axis), grown back if
# needed until it holds BD_REGION_ROOM (default 2.0) times as many slice sites as the cells need.  Everything else is
# placed as usual.  Why: on the automatic flow's routes the wires between cells are 30-40 % of a loop's critical cycle
# (xorshift, research/data/placekeep/README.md's neighbour; cycdecomp.py), and relative-placement groups (BD_RLOC v4 /
# v8) and net weights (ringplace) did not help; a hard region per ring had not been tried.
# Prints "region: N cells in X..X x Y..Y (grid), from M previous cells".
import json, os, re

rx = re.compile(os.environ["BD_REGION_RX"])
src = os.environ["BD_REGION_FROM"]
shrink = float(os.environ.get("BD_REGION_SHRINK", "0.6"))
room = float(os.environ.get("BD_REGION_ROOM", "2.0"))
with open(src) as f:
    d = json.load(f)
top = [m for m in d["modules"].values() if any("NEXTPNR_BEL" in c.get("attributes", {}) for c in m.get("cells", {}).values())][0]
RE_SL = re.compile(r"^SLICE_X(\d+)Y(\d+)/")
locs = []                             # SLICE coordinates (this Python API has no getBelLocation; regions take bel names)
for n, c in top["cells"].items():
    m = RE_SL.match(c.get("attributes", {}).get("NEXTPNR_BEL", ""))
    if m and rx.search(n):
        locs.append((int(m.group(1)), int(m.group(2))))
cells = [(nm, c) for nm, c in ctx.cells if rx.search(nm) and c.type in ("SLICE_LUTX", "SLICE_FFX", "CARRY4", "SELMUX2_1")]
if not locs or not cells:
    print("region: nothing to confine (%d previous cells, %d now)" % (len(locs), len(cells)))
else:
    xs = sorted(x for x, _ in locs)
    ys = sorted(y for _, y in locs)
    cx, cy = xs[len(xs) // 2], ys[len(ys) // 2]
    hw, hh = max(1.0, (xs[-1] - xs[0]) * shrink / 2), max(1.0, (ys[-1] - ys[0]) * shrink / 2)
    need = room * len([1 for _, c in cells if c.type == "SLICE_LUTX"]) / 8.0   # 8 LUT bels per slice
    slice_bels = {}
    for b in ctx.getBels():
        m = RE_SL.match(str(b))
        if m:
            slice_bels.setdefault((int(m.group(1)), int(m.group(2))), []).append(str(b))
    while True:
        x0, x1, y0, y1 = int(cx - hw), int(cx + hw), int(cy - hh), int(cy + hh)
        inside = [k for k in slice_bels if x0 <= k[0] <= x1 and y0 <= k[1] <= y1]
        if len(inside) >= need or hw > 200:
            break
        hw, hh = hw * 1.15 + 1, hh * 1.15 + 1
    ctx.createRectangularRegion("bd_ring", 1, 1, 0, 0)          # empty rectangle; the bels are added by name
    for k in inside:
        for b in slice_bels[k]:
            ctx.addBelToRegion("bd_ring", b)
    for nm, c in cells:
        ctx.constrainCellToRegion(nm, "bd_ring")
    print("region: %d cells in SLICE_X%d..%d Y%d..%d, %d slices for %.0f needed, from %d previous cells (X%d..%d Y%d..%d)"
          % (len(cells), x0, x1, y0, y1, len(inside), need, len(locs), xs[0], xs[-1], ys[0], ys[-1]))
