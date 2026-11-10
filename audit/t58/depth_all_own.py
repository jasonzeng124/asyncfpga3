# T58: own longest summed-smax path inside a unit cone S (same rule as t50/u1_depth_own.py), max over all of S.
# usage: depth_all_own.py NET.json S_FILE...
import json, sys, functools
sys.setrecursionlimit(100000)
gates = json.load(open(sys.argv[1]))["gates"]
for f in sys.argv[2:]:
    S = {int(l.split()[1]) for l in open(f) if l.startswith('S ')}
    drv = {g["out"]: g for g in gates if g["out"] in S}
    @functools.lru_cache(None)
    def depth(n):
        g = drv[n]
        return max([(depth(i) if i in S else 0) + a["smax"] for i, a in zip(g["ins"], g["arcs"])] + [0])
    print(f, len(S), "max depth", max(depth(n) for n in S))
