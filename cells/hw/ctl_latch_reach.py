#!/usr/bin/env python3
"""How far is a bd_link's C node from its OWN latch, and does RLOC help?

verify/converge.sh gives up on gcd and names this as the cause: "the same C
node reaches its own latch across ~1920 ps of routing, while the same C node
reaches its own delay chain in 639".  This measures both out of a build's
routed SDF, and splits the latch sinks by whether hw/rloc_stamp.py actually
grouped them -- which turns an assertion about placement into a number.

  hw/ctl_latch_reach.py build/hw/<top>/<top>
"""
import json, re, sys

def norm(pin):
    s = pin.rsplit("/", 1)[0].replace("\\", "")
    s = re.sub(r"\$LUT[0-9_]*$", "", s)
    return s.split(".", 2)[-1] if s.startswith("bridge_i.udut.") else s

def stats(v):
    v = sorted(v)
    n = len(v)
    return n, v[n // 2], v[int(n * 0.9)], v[-1]

def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    stem = sys.argv[1]
    grouped = set()
    for _, m in json.load(open(stem + ".json"))["modules"].items():
        for cn, c in m.get("cells", {}).items():
            if "RLOC_GROUP" in c.get("attributes", {}):
                grouped.add(cn)
    sdf = open(stem + ".sdf").read()
    pat = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\(([-\d.:]+)\)")
    g, u, chain = [], [], []
    for m in pat.finditer(sdf):
        src, dst, dl = m.groups()
        if ".ctl.u.u" not in src:
            continue
        base = src.split(".ctl.u.u")[0]
        if not dst.startswith(base):
            continue
        tail = dst[len(base):]
        try:
            ps = float(dl.split(":")[-1].strip("()"))
        except ValueError:
            continue
        if ".lat" in tail:
            (g if norm(dst) in grouped else u).append(ps)
        elif ".chain" in tail:
            chain.append(ps)
    print(f"RLOC_GROUP cells in netlist: {len(grouped)}")
    rows = [("C node -> own latch, GROUPED", g),
            ("C node -> own latch, ungrouped", u),
            ("C node -> own delay chain", chain)]
    for lbl, v in rows:
        if not v:
            print(f"  {lbl:32} none")
            continue
        n, med, p90, mx = stats(v)
        print(f"  {lbl:32} n={n:5d}  median {med:6.0f} ps  p90 {p90:6.0f}  max {mx:6.0f}")
    if g and u:
        print(f"\n  grouping is worth {stats(u)[1] - stats(g)[1]:.0f} ps of median "
              f"routing, and covers {100.0*len(g)/(len(g)+len(u)):.1f}% of latch sinks")

main()
