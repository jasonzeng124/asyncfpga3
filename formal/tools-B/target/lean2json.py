#!/usr/bin/env python3
"""Shard B (UNTRUSTED helper): rebuild shard A's decoded-target JSON (the format of
tools-A/target/sim.py) from the GENERATED Lean data Formal/Target/Net/*.lean, so B can run
experiments on exactly the netlist the Lean statement is about.
usage: lean2json.py NETDIR OUT_net.json OUT_arbs.json"""
import json, re, sys, glob, os
d = sys.argv[1]
src = open(os.path.join(d, "Nodes.lean")).read()
names = []
for m in re.finditer(r'def n\d+ : List String := \[(.*?)\]\n', src, re.S):
    names += re.findall(r'"((?:[^"\\]|\\.)*)"', m.group(1))
gates = []
P = re.compile(r'^\s*P "((?:[^"\\]|\\.)*)" (\d+) (\d+) (\d+) (\d+) (\d+) (\d+)[,\]]?$')
G = re.compile(r'^\s*⟨"((?:[^"\\]|\\.)*)", (\d+), (\d+), \[([^\]]*)\], \[(.*)\], (\d+)⟩[,\]]?$')
A = re.compile(r'⟨(\d+), (\d+), (\d+), (\d+)⟩')
for f in sorted(glob.glob(os.path.join(d, "G*.lean"))):
    for line in open(f):
        m = P.match(line)
        if m:
            n, i, o, a, b, c, e = m.groups()
            gates.append({"name": n, "k": 1, "init": 2, "ins": [int(i)],
                          "arcs": [dict(fmin=int(a), fmax=int(b), smin=int(c), smax=int(e))], "out": int(o)})
            continue
        m = G.match(line)
        if m:
            n, k, init, ins, arcs, o = m.groups()
            gates.append({"name": n, "k": int(k), "init": int(init),
                          "ins": [int(x) for x in ins.split(",")] if ins.strip() else [],
                          "arcs": [dict(fmin=int(a), fmax=int(b), smin=int(c), smax=int(e)) for a, b, c, e in A.findall(arcs)],
                          "out": int(o)})
allsrc = open(os.path.join(d, "All.lean")).read()
nG = int(re.search(r"def nGates : Nat := (\d+)", allsrc).group(1))
assert len(gates) == nG, (len(gates), nG)
assert all(g["out"] == i for i, g in enumerate(gates)), "gate i must drive node i"
arbs = [(int(q), [int(x) for x in ins.split(",")]) for q, ins in
        re.findall(r"⟨(\d+), \[([0-9, ]+)\]⟩", allsrc[allsrc.index("def arbs"):])]
json.dump({"nodes": names, "gates": gates}, open(sys.argv[2], "w"))
json.dump([{"q": names[q], "qi": q, "ins": [names[i] for i in ins], "insi": ins} for q, ins in arbs], open(sys.argv[3], "w"), indent=1)
print("nodes", len(names), "gates", len(gates), "arbs", len(arbs))
