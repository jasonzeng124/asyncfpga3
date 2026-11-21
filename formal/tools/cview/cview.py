#!/usr/bin/env python3
"""Shard C (UNTRUSTED generator/explorer): the collapsed view of a decoded Spec netlist.
For every logic gate (not a copy gate: k = 1, INIT 0b10), follow each pin's node back
through copy gates to its source (a node driven by a logic gate, or by no gate).
usage: cview.py net.json [out.json]"""
import json, sys, collections
net = json.load(open(sys.argv[1])); G = net["gates"]; N = net["nodes"]
drv = {g["out"]: i for i, g in enumerate(G)}
assert all(g["out"] == i for i, g in enumerate(G))
def is_copy(g): return g["k"] == 1 and g["init"] == 2
logic = [i for i, g in enumerate(G) if not is_copy(g)]
view = []; lens = collections.Counter(); srcs = collections.Counter(); cyc = 0
for gi in logic:
    g = G[gi]; pins = []
    for u in g["ins"]:
        chain = []; v = u; seen = set()
        while v in drv and is_copy(G[drv[v]]) and v not in seen:
            seen.add(v); chain.append(v); v = G[v]["ins"][0]
        if v in seen: cyc += 1
        pins.append((v, chain)); lens[len(chain)] += 1
        srcs["undriven" if v not in drv else "logic"] += 1
    view.append((gi, pins))
kinds = collections.Counter((G[i]["k"]) for i in logic)
print("gates", len(G), "logic gates", len(logic), "by k", sorted(kinds.items()))
print("pins", sum(lens.values()), "chain length histogram", sorted(lens.items()))
print("sources", dict(srcs), "pure-copy cycles", cyc)
used = set(c for _, ps in view for _, ch in ps for c in ch)
print("copy gates on some chain", len(used), "of", len(G) - len(logic))
if len(sys.argv) > 2: json.dump(view, open(sys.argv[2], "w"))
