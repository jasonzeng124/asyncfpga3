#!/usr/bin/env python3
"""chain_regions.py -- place each matched delay next to the datapath it tracks.

    chain_regions.py <pass-1 gcd_hw_routed.json> <regions.json> [--half-w 2] [--min-half-h 3]
    (then: BD_CHAIN_REGIONS=<regions.json> hw/build_hw.sh ..., which runs
     hw/chain_regions_preplace.py as nextpnr's --pre-place script)

WHY.  A matched delay (`<cell>.<dly>.chain.g[i].u`) bounds its datapath only
while both see the same silicon speed.  Within-die variation is correlated by
position, and the board-fidelity GLS found two genuine failures (BQ#3 seed 9
uori2, BQ#2 seed 6 uori3; JOURNAL 2026-10-29/30) where the placer had put a
chain 20-30 slices from its datapath and the scatter draw made the two regions
differ ~3x in speed.  No timing rule models that.  The fix is placement, not
length: a chain that sits among its datapath's LUTs drifts with them.

WHAT.  From a first route, for every compute cell (one with a request OR,
`<cell>.uor`) that has a chain, take the centroid of the cell's other placed
LUT/CARRY sites and write a rectangle around it: +-half_w slice columns and
+-max(min_half_h, rows the chain needs) slice rows, clipped to the device.
The pre-place script constrains the chain's cells to that rectangle; nothing
else is constrained, so the datapath may move on the second pass (the region
is then off-centre; chain_dist.py measures what actually happened).

Coordinates are SLICE_X/Y site indices; the pre-place script converts them to
nextpnr grid locations through the bels themselves.
"""
import argparse, json, re, sys
from collections import defaultdict

RE_CHAIN = re.compile(r"^(?P<base>.+)\.chain\.g\[(?P<i>\d+)\]\.u(?:$|\.)")
RE_SITE = re.compile(r"SLICE_X(\d+)Y(\d+)")


def site(c):
    m = RE_SITE.match(c.get("attributes", {}).get("NEXTPNR_BEL", ""))
    return (int(m.group(1)), int(m.group(2))) if m else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("routed"); ap.add_argument("out")
    ap.add_argument("--half-w", type=int, default=2)
    ap.add_argument("--min-half-h", type=int, default=3)
    a = ap.parse_args()
    cells = list(json.load(open(a.routed))["modules"].values())[0]["cells"]
    xs = [s[0] for s in map(site, cells.values()) if s]; ys = [s[1] for s in map(site, cells.values()) if s]
    X1, Y1 = max(xs), max(ys)
    chains = defaultdict(list)
    for n in cells:
        m = RE_CHAIN.match(n)
        if m:
            chains[m.group("base")].append(n)
    by_parent = defaultdict(list)
    for n, c in cells.items():
        s = site(c)
        if s and not RE_CHAIN.match(n):
            by_parent[n.split("$", 1)[0]].append(s)
    out = {}
    for base, members in sorted(chains.items()):
        parent = base.rpartition(".")[0]
        if (parent + ".uor") not in by_parent:
            continue                       # only compute cells (rule A's)
        dp = [s for p, ss in by_parent.items() if p.startswith(parent + ".") for s in ss]
        if not dp:
            continue
        cx = round(sum(x for x, _ in dp) / len(dp)); cy = round(sum(y for _, y in dp) / len(dp))
        hh = max(a.min_half_h, (len(members) + 7) // 8 + 1)
        out[base] = {"x0": max(0, cx - a.half_w), "x1": min(X1, cx + a.half_w),
                     "y0": max(0, cy - hh), "y1": min(Y1, cy + hh),
                     "cells": sorted(members), "dp_centroid": [cx, cy], "dp_cells": len(dp)}
    json.dump(out, open(a.out, "w"), indent=1)
    print(f"chain_regions: {len(out)} chains constrained (half_w {a.half_w}, min_half_h {a.min_half_h})")


if __name__ == "__main__":
    sys.exit(main())
