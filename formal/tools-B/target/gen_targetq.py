#!/usr/bin/env python3
"""Shard B: print the `targetQ` rows of Formal/Cells/ArbClean.lean (name, k, INIT, roles of each target
ustate O6 gate) from lean2json.py output. usage: gen_targetq.py NET.json ARBS.json BND.json"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.argv = sys.argv[:4] + ["0,1"]
src = open(os.path.join(HERE, "adv.py")).read(); src = src[:src.index('base, res0 = run({}, "base")')]
ns = {"__file__": os.path.join(HERE, "adv.py")}; exec(compile(src, "adv.py", "exec"), ns)
g = ns["g"]; rows = []
for a in ns["A"]:
    R = ns["roles"](a); G = g[R["q"]]; ins = G["ins"]
    r = {k: ins.index(v) for k, v in R.items() if k != "q"}
    tied = [i for i in range(G["k"]) if i not in r.values()]
    rows.append('  ("%s", %d, 0x%x, ⟨%d, %d, %d, %d, %d, [%s]⟩)' % (G["name"], G["k"], G["init"], r["r1"], r["r2"],
                r["fb"], r["rst"], r["a0"], ", ".join("(%d, true)" % t for t in tied)))
print(",\n".join(rows))
