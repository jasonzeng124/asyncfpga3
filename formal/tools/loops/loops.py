#!/usr/bin/env python3
"""Shard C (UNTRUSTED explorer): loop structure of a decoded Spec netlist (lean2json format).
A gate's pin is a SELF-FEEDBACK pin if following its node back through copy gates
(k = 1, INIT 0b10) reaches the gate's own output. Cut every self-feedback pin and report
whether the remaining node graph is acyclic; if not, list the remaining cycles' gates.
usage: loops.py net.json [out_cut.json]"""
import json, sys, collections
net = json.load(open(sys.argv[1]))
G = net["gates"]; names = net["nodes"]; n = len(names)
drv = {g["out"]: i for i, g in enumerate(G)}
def is_copy(g): return g["k"] == 1 and g["init"] == 2
cuts = []   # (gate index, pin index, chain of copy gate indices from g.out to the pin node)
for gi, g in enumerate(G):
    if g["k"] < 2: continue
    for j, u in enumerate(g["ins"]):
        chain = []; v = u; seen = set()
        while v != g["out"] and v in drv and is_copy(G[drv[v]]) and v not in seen:
            seen.add(v); chain.append(drv[v]); v = G[drv[v]]["ins"][0]
        if v == g["out"]:
            cuts.append((gi, j, chain[::-1]))
cutset = {(gi, j) for gi, j, _ in cuts}
# graph on nodes: edge pin node -> gate out, except cut pins
def depends(g, j):
    k, I = g["k"], g["init"]
    return any(((I >> a) & 1) != ((I >> (a ^ (1 << j))) & 1) for a in range(1 << k))
nodep = {(gi, j) for gi, g in enumerate(G) for j in range(g["k"]) if not depends(g, j)}
print("pins outside their INIT's support:", len(nodep))
succ = collections.defaultdict(list)
for gi, g in enumerate(G):
    for j, u in enumerate(g["ins"]):
        if (gi, j) not in cutset and (gi, j) not in nodep: succ[u].append(g["out"])
# iterative Tarjan
index = {}; low = {}; onst = set(); st = []; sccs = []; idx = 0
for root in range(n):
    if root in index: continue
    work = [(root, 0)]
    index[root] = low[root] = idx; idx += 1; st.append(root); onst.add(root)
    while work:
        v, i = work[-1]
        if i < len(succ[v]):
            work[-1] = (v, i + 1); w = succ[v][i]
            if w not in index:
                index[w] = low[w] = idx; idx += 1; st.append(w); onst.add(w); work.append((w, 0))
            elif w in onst: low[v] = min(low[v], index[w])
        else:
            work.pop()
            if work: low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = st.pop(); onst.discard(w); comp.append(w)
                    if w == v: break
                if len(comp) > 1 or v in succ[v]: sccs.append(comp)
kinds = collections.Counter((G[gi]["k"], G[gi]["init"]) for gi, _, _ in cuts)
print("gates", len(G), "self-feedback pins", len(cuts), "gates with one", len({gi for gi, _, _ in cuts}))
print("chain lengths", collections.Counter(len(c) for _, _, c in cuts))
print("cut gates by (k, init):", kinds.most_common(12))
print("cyclic SCCs after the cut:", len(sccs), "sizes", sorted(len(c) for c in sccs)[-10:])
for c in sccs[:5]:
    gs = [drv[v] for v in c if v in drv]
    print(" SCC:", [(names[G[g]["out"]], G[g]["k"], hex(G[g]["init"])) for g in gs if G[g]["k"] > 1][:12])
if len(sys.argv) > 2:
    json.dump({"cuts": cuts, "sccs": sccs}, open(sys.argv[2], "w"))
