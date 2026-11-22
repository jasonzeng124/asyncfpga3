# nextpnr --pre-place script for hw/chain_regions.py's regions file.
# The file path comes from the BD_CHAIN_REGIONS environment variable.  This
# nextpnr's Python bels are bare name strings with no location call, so each
# region is made from bel names: a degenerate rectangle at grid (0,0) (no
# slice there) plus addBelToRegion for every bel of every SLICE_X/Y site in
# the requested rectangle.
import json, os, re

regions = json.load(open(os.environ["BD_CHAIN_REGIONS"]))
RE = re.compile(r"^SLICE_X(\d+)Y(\d+)/")
by_site = {}
for bel in ctx.getBels():
    m = RE.match(bel)
    if m:
        by_site.setdefault((int(m.group(1)), int(m.group(2))), []).append(bel)
n_cells = n_miss = n_bels = 0
for i, (base, r) in enumerate(sorted(regions.items())):
    name = "chainreg%d" % i
    ctx.createRectangularRegion(name, 0, 0, 0, 0)
    k = 0
    for x in range(r["x0"], r["x1"] + 1):
        for y in range(r["y0"], r["y1"] + 1):
            for bel in by_site.get((x, y), ()):
                ctx.addBelToRegion(name, bel); k += 1
    n_bels += k
    if k == 0:
        print("chain_regions: no slices in the rectangle of", base); n_miss += len(r["cells"]); continue
    for c in r["cells"]:
        if c in ctx.cells:
            ctx.constrainCellToRegion(c, name); n_cells += 1
        else:
            n_miss += 1
print("chain_regions: %d regions, %d bels, %d cells constrained, %d missing" % (len(regions), n_bels, n_cells, n_miss))
