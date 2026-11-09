# T52: own longest slow-max path through C's uselect1 cone S (decoded netlist): depth(n) = max over the driving gate's pins i of
# (depth(src_i) if src_i in S else 0) + smax(arc_i); report max over the 32 z nodes and over all of S. C's D = 8815 ps.
import json, sys, functools
sys.setrecursionlimit(100000)
net = json.load(open(sys.argv[1])); gates = net["gates"]
S, Z = set(), []
for l in open(sys.argv[2]):
    f = l.split()
    if f[0] == 'S': S.add(int(f[1]))
    elif f[0] == 'IO': Z.append(int(f[4]))
drv = {g["out"]: g for g in gates if g["out"] in S}
@functools.lru_cache(None)
def depth(n):
    g = drv[n]
    return max([(depth(i) if i in S else 0) + a["smax"] for i, a in zip(g["ins"], g["arcs"])] + [0])
print("max depth over z nodes", max(depth(z) for z in Z), "over all S", max(depth(n) for n in S))
