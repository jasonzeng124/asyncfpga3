#!/usr/bin/env python3
"""rloc_dist.py -- the three interconnect distributions an RLOC_GROUP is
supposed to move, read straight off a routed SDF.

    C -> latch    a link's C node to the ENABLE pin of one of its own latch
                  LUTs.  This is the term that costs latency on every data
                  transfer and, at a select, half of rule E's t_sel.
    C -> chain    the same C node to the first element of its own matched
                  delay chain.  The control here: a string of single-load
                  nets the placer already keeps together.
    latch -> sel  a latch LUT output to a bd_mux join's or bd_steer's select
                  pin.  The other half of t_sel -- and the one at risk of
                  ABSORBING the first, since the latch's fanout is what pulled
                  it away from its C node to begin with.

Only routed net delay is counted -- (INTERCONNECT src dst (v:v:v)) -- never
cell arcs, because a cluster constraint cannot change a cell arc and including
them would dilute the very number being tested.

n counts LOADS, not links: a W=32 link's C node drives sixteen latch LUTs and
each is one sample here.

usage: rloc_dist.py <routed.sdf> [<routed.sdf> ...]
"""

import re
import sys
import pathlib

RE_IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):")
RE_LINK = re.compile(r"(?:^|\.)(ulink_[A-Za-z0-9_]+)\.")
RE_CNODE = re.compile(
    r"(?:^|\.)(?P<link>ulink_[A-Za-z0-9_]+)\."
    r"(?:ctl\.u\.u|many\.(?:cpair\[\d+\]|codd)\.u\.u)/O")
RE_SELPIN = re.compile(r"\.(?:uj0|uj1|u)/A\d$")


def unescape(s):
    return s.replace("\\", "")


def pct(v, q):
    if not v:
        return 0
    v = sorted(v)
    i = min(len(v) - 1, int(round(q * (len(v) - 1))))
    return v[i]


def summarise(name, v):
    if not v:
        return f"  {name:<22} n=0"
    return (f"  {name:<22} n={len(v):<6} min={min(v):<6} p50={pct(v, .5):<6} "
            f"p90={pct(v, .9):<6} max={max(v):<6} mean={sum(v) // len(v)}")


def measure(path, selpins):
    """-> (C->latch, C->chain, latch->select, latch->anything, every net hop)

    The last two are the null-result check.  A cluster cannot destroy
    interconnect delay, only move it: the latch was pulled away from its C node
    by its own OUTPUT fanout, so pinning it next to the C node may simply
    reappear as a longer latch output.  `latch -> anything` is that term for
    every load a latch drives, and the whole-design hop distribution says
    whether the constraint cost the rest of the route anything.
    """
    to_latch, to_chain, to_sel, from_latch, allhops = [], [], [], [], []
    for line in path.read_text().splitlines():
        m = RE_IC.search(line)
        if not m:
            continue
        src, dst, d = unescape(m.group(1)), unescape(m.group(2)), int(m.group(3))
        allhops.append(d)
        c = RE_CNODE.search(src)
        if c:
            link = c.group("link")
            dm = RE_LINK.search(dst)
            if dm and dm.group(1) == link:
                tail = dst.split(link, 1)[1]
                if ".lat" in tail:
                    to_latch.append(d)
                elif ".rdly.chain.g[0]." in tail:
                    to_chain.append(d)
            continue
        if ".lat" in src and RE_LINK.search(src):
            from_latch.append(d)
            if dst in selpins:
                to_sel.append(d)
    return to_latch, to_chain, to_sel, from_latch, allhops


def select_pins(sdf):
    """Physical select pins, from the routed netlist next to the SDF -- the
    same X_ORIG_PORT_A<k> permutation record verify/tighten.py decodes, so a
    pin is named because the packer says the select landed there."""
    import json
    jp = sdf.with_name(sdf.stem + "_routed.json")
    if not jp.exists():
        return set()
    top = list(json.loads(jp.read_text())["modules"].values())[0]
    cells = top.get("cells", {})
    out = set()
    for name, cell in cells.items():
        base = name.rsplit(".", 1)[0] if "." in name else ""
        tag = name.rsplit(".", 1)[-1]
        tag = re.sub(r"\$LUT\d+$", "", tag)
        if tag in ("uj0", "uj1"):
            want = "I2"
        elif tag == "u" and (base + ".uack") in cells:
            want = "I1"
        else:
            continue
        attrs = cell.get("attributes", {})
        for k in range(1, 7):
            if attrs.get(f"X_ORIG_PORT_A{k}") == want:
                out.add(f"{name}/A{k}")
    return out


def main():
    for a in sys.argv[1:]:
        p = pathlib.Path(a)
        sp = select_pins(p)
        lat, ch, sel, fl, allh = measure(p, sp)
        print(f"{p}")
        print(f"  ({len(sp)} select pin(s) located in the routed netlist)")
        print(summarise("C -> own latch", lat))
        print(summarise("C -> own chain g[0]", ch))
        print(summarise("latch -> select pin", sel))
        print(summarise("latch -> any load", fl))
        print(summarise("every net hop", allh))
        print(f"  {'total routed delay':<22} {sum(allh) / 1e6:.3f} us over "
              f"{len(allh)} hops")
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
