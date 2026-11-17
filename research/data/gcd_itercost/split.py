#!/usr/bin/env python3
"""split.py GRAPHDIR [EDIT ...] -- the critical cycle of an eventgraph graph, in visit order, each visit of a stage
split into: rise chain (delay-role nodes, wire+arc), rise logic, rise handshake-wire, rise handshake-arc, fall (RTZ)
chain, fall other.  Also the number of chain elements of each line crossed on the rise."""
import sys, os, collections, re
sys.path.insert(0, "/home/user/asyncfpga3/research/tools/eventgraph")
import whatif
g = whatif.G(sys.argv[1])
for ed in sys.argv[2:]: g.apply(ed)
lam, cyc = g.period()
arcs = [g.arcs[i] for i in cyc]
# rotate to start at the max-weight stage boundary for readability: start where inst changes
rows = []
cur = None
for a in arcs:
    v = g.nodes[a["v"]]; u = g.nodes[a["u"]]
    inst = v["inst"]
    if cur is None or cur["inst"] != inst:
        cur = dict(inst=inst, rch=0, rlog=0, rhw=0, rha=0, fch=0, fot=0, elems=set(), edges=[]); rows.append(cur)
    w = a["w"]
    # wire / arc split from arcs.tsv (not kept by whatif.G): reload lazily
    cur["edges"].append((a["u"], a["v"], w, v["edge"], v.get("role", "")))
    if v["edge"] == "F":
        if v.get("role") == "delay": cur["fch"] += w
        else: cur["fot"] += w
    else:
        if v.get("role") == "delay":
            cur["rch"] += w
            m = whatif.CHAIN.search(v.get("cell", ""))
            if m: cur["elems"].add(v["cell"].split(".chain")[0] + "#" + m.group(2))
        elif v.get("role") == "logic": cur["rlog"] += w
        else:
            cur["rhw"] += w   # wire+arc; split below
# wire/arc split for handshake arcs
wa = {}
with open(sys.argv[1] + "/arcs.tsv") as f:
    h = f.readline().rstrip("\n").split("\t")
    for l in f:
        r = dict(zip(h, l.rstrip("\n").split("\t")))
        wa[(int(r["u"]), int(r["v"]), r["pin"])] = (int(r["wire_ps"]), int(r["arc_ps"]))
for row, a0 in zip(rows, [None] * len(rows)): pass
for row in rows:
    hw = ha = 0
    for (u, v, w, e, role) in row["edges"]:
        if e == "R" and role not in ("delay", "logic"):
            cands = [x for k, x in wa.items() if k[0] == u and k[1] == v]
            wi, ar = cands[0] if cands else (w, 0)
            hw += wi; ha += ar
    row["rhw"], row["rha"] = hw, ha
tot = collections.Counter()
print("period %.0f ps, %d arcs, %d stage visits" % (lam, len(arcs), len(rows)))
print("%-36s %7s %7s %7s %7s %7s %7s %7s %5s" % ("stage", "total", "r.chain", "r.logic", "r.hwire", "r.harc", "f.chain", "f.other", "elems"))
for r in rows:
    t = r["rch"] + r["rlog"] + r["rhw"] + r["rha"] + r["fch"] + r["fot"]
    for k in ("rch", "rlog", "rhw", "rha", "fch", "fot"): tot[k] += r[k]
    print("%-36s %7d %7d %7d %7d %7d %7d %7d %5d" % (r["inst"], t, r["rch"], r["rlog"], r["rhw"], r["rha"], r["fch"], r["fot"], len(r["elems"])))
print("%-36s %7d %7d %7d %7d %7d %7d %7d" % ("TOTAL", sum(tot.values()), tot["rch"], tot["rlog"], tot["rhw"], tot["rha"], tot["fch"], tot["fot"]))
