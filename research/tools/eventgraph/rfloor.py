#!/usr/bin/env python3
"""rfloor.py GRAPHDIR... (subagent ringfuse, 2026-11-19): the rising-only floor cycle (max cycle ratio over arcs between R nodes only) of a timed event
graph, decomposed per kernel instance: chain (arcs into a matched-delay chain element of that instance, its cell + the
chain's own wire), in-wire (wire of the arc entering the instance from another instance: the hop), other (cell arcs and
intra wires: C-elements, joins, uor, LUT logic)."""
import os, re, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import maxplus
from cycle_wire import load, inst_of
CH = re.compile(r"\.(udly|rdly|uack|us)\.chain\.g\[(\d+)\]")
for d in sys.argv[1:]:
    nodes, arcs, P = load(d)
    keep = [i for i, a in enumerate(arcs) if nodes[a["u"]].get("edge") == "R" and nodes[a["v"]].get("edge") == "R"]
    sub = [arcs[i] for i in keep]
    lam, cyc = maxplus.mcr(len(nodes), sub, lenient=True)
    tot = collections.OrderedDict(); T = dict(chain=0, inter=0, other=0)
    for i in cyc:
        a = sub[i]; cu, cv = nodes[a["u"]]["cell"], nodes[a["v"]]["cell"]
        iu, iv = inst_of(cu), inst_of(cv)
        r = tot.setdefault(iv, dict(chain=0, inter=0, other=0, n=0))
        if iu != iv:
            r["inter"] += a["wire"]; T["inter"] += a["wire"]
            x = a["arc"]
        else:
            x = a["wire"] + a["arc"]
        if CH.search(cv):
            r["chain"] += x; T["chain"] += x; r["n"] += 1
        else:
            r["other"] += x; T["other"] += x
    tw = sum(sub[i]["wire"] for i in cyc)
    print("== %s P=%s R-floor %d ps (%d arcs, tokens %d; wire %d ps = %.0f%%)" % (os.path.basename(d.rstrip('/')), P, sum(sub[i]['w'] for i in cyc), len(cyc), sum(sub[i]['o'] for i in cyc), tw, 100.0 * tw / max(1, sum(sub[i]['w'] for i in cyc))))
    for k, r in tot.items():
        print("   %-28s total %5d = hop-wire %5d + chain %5d (%2d el) + other %5d" % (k, r["inter"] + r["chain"] + r["other"], r["inter"], r["chain"], r["n"], r["other"]))
    print("   TOTAL hop-wire %d  chain %d  other %d  = %d" % (T["inter"], T["chain"], T["other"], sum(T.values())))
