#!/usr/bin/env python3
"""lever.py GRAPHDIR EDIT [EDIT ...] -- whatif.py's edits plus
    shrink:INST:N    every chain of INST (udly/rdly/uack) keeps its first N elements: arcs into elements g[i], i >= N,
                     cost 0 (both edges).  A line shortened to N elements, at the route's own per-element cost.
    fastfall:BDC     search.py's BDC_LINK_FASTFALL edit
    stage:/depth:/fastfall:INST/nofall as whatif.py
Prints the predicted period and the cycle's stages."""
import sys, re
sys.path.insert(0, "/home/user/asyncfpga3/research/tools/eventgraph")
import whatif, search

def shrink(g, inst, n, kind=None):
    k = 0
    for a in g.arcs:
        nv, nu = g.nodes[a["v"]], g.nodes[a["u"]]
        if nv["inst"] != inst: continue
        m = whatif.CHAIN.search(nv.get("cell", ""))
        if kind and m:
            c = nv["cell"]
            if kind in ("udly", "rdly", "uack") and m.group(1) != kind: continue
            if kind == "rdly" and "many.stage" in c and "stage[%d]" % (c.count("x")) and False: pass
            if kind.startswith("stage") and ("stage[%s]" % kind[5:]) not in c: continue
            if kind == "rdly" and "many.stage" in c: continue
        if m and int(m.group(2)) >= n and nu["inst"] == inst and whatif.CHAIN.search(nu.get("cell", "")):
            a["w"] = 0; k += 1
    if not k: raise ValueError("shrink: nothing on %s" % inst)
    return g

def apply(g, ed):
    p = ed.split(":")
    if p[0] == "shrink": return shrink(g, p[1], int(p[2]), p[3] if len(p) > 3 else None)
    return search.apply(g, ed)

if __name__ == "__main__":
    g = whatif.G(sys.argv[1])
    base, _ = g.period()
    g2 = g.copy()
    for ed in sys.argv[2:]: apply(g2, ed)
    lam, cyc = g2.period()
    by, flips = g2.describe(cyc)
    print("base %.0f  edited %.0f  delta %+.0f  (%s)" % (base, lam, lam - base, " ".join(sys.argv[2:])))
    print("  cycle: " + ", ".join("%s %d/%d" % (k, r, f) for k, (r, f) in by.items()))
    print("  polarity changes: " + ", ".join(flips))
