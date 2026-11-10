# T62: own collapsed start bound at g = 1, kappa = 0 (P1Defs.cStartN re-implemented from its definition):
# cStartN(g) = max_i smax(arc_i) + sum_i [ sum over the copy chain behind pin i (k=1, init=2 gates c) of
# (startN c + smax(arc0 c)) + smax(arc_i) ].  Reports the max over C's reset-island members (claim A2 = 19,832) and,
# for comparison, over every non-copy gate of my decode (B's startPS bound 33,002 uses KEPT pins only, so mine may be
# larger there). usage: a2_own.py NET.json RISL_DUMP
import json, sys
G = json.load(open(sys.argv[1])); gates = G["gates"]; drv = {g["out"]: g for g in gates}
names = {}
for n in G["nodes"] if isinstance(G["nodes"], list) else []:
    pass
def stN(g): return max([a["smax"] for a in g["arcs"]] + [0])
def cstart(g):
    tot = stN(g)
    for n, a in zip(g["ins"], g["arcs"]):
        s = 0
        while n in drv and drv[n]["k"] == 1 and drv[n]["init"] == 2:
            c = drv[n]; s += stN(c) + c["arcs"][0]["smax"]; n = c["ins"][0]
        tot += s + a["smax"]
    return tot
mem = [int(l.split()[0]) for l in open(sys.argv[2])]
print("reset island: max cStartN", max((cstart(drv[w]), w) for w in mem))
allg = [(cstart(g), g["out"], g.get("name")) for g in gates if not (g["k"] == 1 and g["init"] == 2)]
allg.sort(reverse=True); print("all non-copy gates: top 3", allg[:3])
