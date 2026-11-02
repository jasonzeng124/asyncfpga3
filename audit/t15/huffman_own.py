#!/usr/bin/env python3
"""huffman_own.py (audit T15): on the auditor's own decode of the target, recount C's HuffmanPS claim:
storage nodes = logic (non-copy) gates with a pin whose source, traced through one-input copy gates, is the gate's own
output; combinational = the other logic gates of the circuit (gates driving environment nodes removed). Is the
combinational pin-to-source graph acyclic, and what is its depth?
    python3 -I huffman_own.py NET.json BND.json
Copy gate here = a one-input gate whose output equals its input (INIT 0b10): pips, pseudo pips, hops."""
import json, sys, collections
N = json.load(open(sys.argv[1])); B = json.load(open(sys.argv[2]))
G = N["gates"]; names = N["nodes"]; idx = {n: i for i, n in enumerate(names)}
env = set(idx[x] for x in B["env"]) if "env" in B and isinstance(B["env"], list) and B["env"] and isinstance(B["env"][0], str) else set(B.get("env", []))
drv = {g["out"]: g for g in G}
copy = lambda g: g["k"] == 1 and g["init"] == 2
def src(n):
    seen = 0
    while True:
        g = drv.get(n)
        if g is None or not copy(g) or g["out"] in env: return n
        n = g["ins"][0]; seen += 1
logic = [g for g in G if not copy(g) and g["out"] not in env]
pins = {g["out"]: [src(i) for i in g["ins"]] for g in logic}
stor = {o for o, ps in pins.items() if o in ps}
comb = {o for o in pins if o not in stor}
kinds = collections.Counter(drv[o]["kind"] for o in stor)
print("logic gates", len(logic), "storage", len(stor), dict(kinds), "combinational", len(comb), "env nodes", len(env))
# acyclicity of comb -> comb source links, longest path (Kahn)
indeg = {o: 0 for o in comb}; succ = collections.defaultdict(list)
for o in comb:
    for s in set(pins[o]):
        if s in comb: succ[s].append(o); indeg[o] += 1
q = [o for o in comb if indeg[o] == 0]; depth = {o: 0 for o in q}; done = 0
while q:
    s = q.pop(); done += 1
    for o in succ[s]:
        depth[o] = max(depth.get(o, 0), depth[s] + 1); indeg[o] -= 1
        if indeg[o] == 0: q.append(o)
print("combinational acyclic:", done == len(comb), "(ordered %d of %d), max depth %d" % (done, len(comb), max(depth.values())))
