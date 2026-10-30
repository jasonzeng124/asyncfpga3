# nextpnr --pre-place script for hw/chain_regions.py's regions file.
# The file path comes from the BD_CHAIN_REGIONS environment variable.  Site
# coordinates (SLICE_X/Y) are turned into grid locations by looking the bels
# up, since the grid has interconnect columns between CLBs.
import json, os

regions = json.load(open(os.environ["BD_CHAIN_REGIONS"]))
loc = {}
for bel in ctx.getBels():
    n = ctx.getBelName(bel)
    if n.startswith("SLICE_X") and n.endswith("/A6LUT"):
        s = n.split("/")[0][len("SLICE_X"):]
        x, y = s.split("Y")
        l = ctx.getBelLocation(bel)
        loc[(int(x), int(y))] = (l.x, l.y)
n_cells = n_miss = 0
for i, (base, r) in enumerate(sorted(regions.items())):
    corners = [loc[(x, y)] for x in range(r["x0"], r["x1"] + 1) for y in range(r["y0"], r["y1"] + 1)
               if (x, y) in loc]
    if not corners:
        print("chain_regions: no slices in the rectangle of", base); n_miss += 1; continue
    gx0 = min(c[0] for c in corners); gx1 = max(c[0] for c in corners)
    gy0 = min(c[1] for c in corners); gy1 = max(c[1] for c in corners)
    name = "chainreg%d" % i
    ctx.createRectangularRegion(name, gx0, gy0, gx1, gy1)
    for c in r["cells"]:
        if c in ctx.cells:
            ctx.constrainCellToRegion(c, name); n_cells += 1
        else:
            n_miss += 1
print("chain_regions: %d regions, %d cells constrained, %d missing" % (len(regions), n_cells, n_miss))
