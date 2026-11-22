#!/usr/bin/env python3
"""cycdecomp.py GRAPHDIR... : critical cycle of an event graph, per kernel instance: chain (arcs INTO a matched-delay
chain element, wire + cell), inter (wire of arcs between instances), other (the rest: C-elements, LUT logic)."""
import os, re, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import maxplus
from cycle_wire import load, inst_of
CH = re.compile(r"\.(udly|rdly|uack|us)\.chain\.g\[(\d+)\]")
for d in sys.argv[1:]:
    nodes, arcs, P = load(d)
    lam, cyc = maxplus.mcr(len(nodes), arcs)
    tot = collections.OrderedDict(); T = dict(chain=0, inter=0, other=0); nel = collections.Counter()
    for i in cyc:
        a = arcs[i]; cu, cv = nodes[a["u"]]["cell"], nodes[a["v"]]["cell"]
        iu, iv = inst_of(cu), inst_of(cv)
        r = tot.setdefault(iv, dict(chain=0, inter=0, other=0, n=0))
        if CH.search(cv):
            r["chain"] += a["wire"] + a["arc"]; T["chain"] += a["wire"] + a["arc"]; r["n"] += 1
            if iu != iv: r["chain"] -= a["wire"]; T["chain"] -= a["wire"]; r["inter"] += a["wire"]; T["inter"] += a["wire"]
        elif iu != iv:
            r["inter"] += a["wire"]; T["inter"] += a["wire"]; r["other"] += a["arc"]; T["other"] += a["arc"]
        else:
            r["other"] += a["wire"] + a["arc"]; T["other"] += a["wire"] + a["arc"]
    print("== %s P=%s cycle %d arcs, tokens %d" % (os.path.basename(d.rstrip('/')), P, len(cyc), sum(arcs[i]['o'] for i in cyc)))
    for k, r in tot.items():
        print("   %-28s chain %5d (%2d el)  inter-wire %5d  other %5d" % (k, r["chain"], r["n"], r["inter"], r["other"]))
    print("   TOTAL chain %d  inter-wire %d  other %d  = %d" % (T["chain"], T["inter"], T["other"], sum(T.values())))
