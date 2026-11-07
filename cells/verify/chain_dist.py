#!/usr/bin/env python3
"""chain_dist.py -- how far each matched delay sits from the datapath it tracks.

    chain_dist.py <gcd_hw_routed.json> [--region N] [--top K]

A matched delay (`<cell>.<dly>.chain.g[i].u`) only tracks its datapath (every
other cell under `<cell>.`) while both see the same silicon speed.  Within-die
variation is correlated by position, so the distance between the two is the
exposure: on BQ#3 seed 9 a chain ~30 slice rows from the comparator it covers
failed under 2x region scatter (JOURNAL 2026-10-29), and none of the timing
rules model it.  This is a SCREEN, not a check: it says where to look and it
ranks candidates for placement constraints; it never passes or fails a build.

Per chain: its centroid, the datapath centroid, the largest chain-to-datapath-
cell distance (Manhattan, in slices; a CLB column pair counts as 2 X), and how
many datapath cells fall outside the chain's scatter region (gen.py's
GLS_REGION_SLICES grid, default 10).

Only compute cells (those with a request OR, `<cell>.uor`, the cells rule A
audits) are listed unless --all: a link's or a rig's chain bounds something
other than the logic under its parent.
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
    ap.add_argument("routed")
    ap.add_argument("--region", type=int, default=10)
    ap.add_argument("--top", type=int, default=25)
    ap.add_argument("--all", action="store_true")
    a = ap.parse_args()
    cells = list(json.load(open(a.routed))["modules"].values())[0]["cells"]
    chains = defaultdict(list)
    for n, c in cells.items():
        m = RE_CHAIN.match(n)
        if m and site(c):
            chains[m.group("base")].append(site(c))
    by_parent = defaultdict(list)
    for n, c in cells.items():
        s = site(c)
        if s and not RE_CHAIN.match(n):
            by_parent[n.split("$", 1)[0]].append(s)   # yosys suffixes start with $
    rows = []
    for base, cs in chains.items():
        parent = base.rpartition(".")[0]
        if not a.all and (parent + ".uor") not in by_parent:
            continue
        dp = [s for p, ss in by_parent.items()
              if p.startswith(parent + ".") for s in ss]
        if not dp:
            continue
        cx = sum(x for x, _ in cs) / len(cs); cy = sum(y for _, y in cs) / len(cs)
        dx = sum(x for x, _ in dp) / len(dp); dy = sum(y for _, y in dp) / len(dp)
        far = max(min(abs(x - u) + abs(y - v) for u, v in cs) for x, y in dp)
        regs = {(x // a.region, y // a.region) for x, y in cs}
        out = sum((x // a.region, y // a.region) not in regs for x, y in dp)
        rows.append((far, abs(cx - dx) + abs(cy - dy), base, len(cs), len(dp), out,
                     (min(x for x, _ in cs), max(x for x, _ in cs), min(y for _, y in cs), max(y for _, y in cs)),
                     (min(x for x, _ in dp), max(x for x, _ in dp), min(y for _, y in dp), max(y for _, y in dp))))
    rows.sort(reverse=True)
    print(f"{len(rows)} matched delays with a datapath; region {a.region}x{a.region} slices")
    print("far  cdist  links  dp  dp_out  chain_bbox(x0-x1,y0-y1)  dp_bbox  chain")
    for far, cd, base, n, nd, out, cb, db in rows[:a.top]:
        print(f"{far:3d}  {cd:5.1f}  {n:5d}  {nd:3d}  {out:6d}  X{cb[0]}-{cb[1]} Y{cb[2]}-{cb[3]}  "
              f"X{db[0]}-{db[1]} Y{db[2]}-{db[3]}  {base}")
    if rows:
        fs = sorted(r[0] for r in rows)
        print(f"far: median {fs[len(fs)//2]}, p90 {fs[int(.9*(len(fs)-1))]}, max {fs[-1]}")


if __name__ == "__main__":
    sys.exit(main())
