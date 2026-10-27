#!/usr/bin/env python3
"""Where does a kernel's matched delay go, and is it logic or routing?

A matched delay is sized to cover its cell's own datapath, so asking what the
delay costs is asking what the datapath costs.  This splits each delay-bearing
cell's cone into interconnect and cell arcs straight out of the routed SDF.

CAVEAT, and it matters: these are SUMS OVER EVERY ARC in the cone, not a
critical path.  Read the ratio as "what this cell's delay is made of", not as
a path length.  verify/tighten.py's `peak` is the path number.

  hw/delay_budget.py build/hw/<top>/<top> [cell ...]
"""
import collections, re, sys


def val(d):
    try:
        return float(d.split(":")[-1].strip("()"))
    except ValueError:
        return None


def main():
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    stem = sys.argv[1]
    sdf = open(stem + ".sdf").read()
    want = sys.argv[2:]
    if not want:
        want = sorted({m.group(1) for m in
                       re.finditer(r"udut\.([a-z][a-z0-9_]*?)\.", sdf.replace("\\", ""))})
    rt, lg, nr, nl = (collections.Counter() for _ in range(4))
    for _, dst, d in re.findall(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\(([-\d.:]+)\)", sdf):
        v = val(d)
        if v is None:
            continue
        clean = dst.replace("\\", "")
        for c in want:
            if f".{c}." in clean:
                rt[c] += v
                nr[c] += 1
    for blk in re.split(r"\(CELL\s", sdf):
        m = re.search(r"\(INSTANCE\s+([^\)]*)\)", blk)
        if not m:
            continue
        inst = m.group(1).strip().replace("\\", "")
        for c in want:
            if f".{c}." in inst or inst.endswith("." + c):
                for d in re.findall(r"\(IOPATH\s+\S+\s+\S+\s+\(([-\d.:]+)\)", blk):
                    v = val(d)
                    if v is not None:
                        lg[c] += v
                        nl[c] += 1
    print(f"{'cell':14}{'routing ps':>12}{'arcs':>7}{'logic ps':>11}{'arcs':>7}{'routing%':>10}")
    for c in want:
        t = rt[c] + lg[c]
        if t:
            print(f"{c:14}{rt[c]:12.0f}{nr[c]:7d}{lg[c]:11.0f}{nl[c]:7d}{100*rt[c]/t:9.1f}%")


main()
