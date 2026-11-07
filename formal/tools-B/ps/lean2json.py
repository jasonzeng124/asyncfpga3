#!/usr/bin/env python3
"""Shard B (UNTRUSTED), 2026-11-07: rebuild the decoded target's net.json (build_net.py's format: nodes, gates with
name/k/init/ins/arcs{fmin,fmax,smin,smax}/out) from the GENERATED Lean data formal/lean/Formal/Target/NetPS
(Nodes.lean n00.., G000..G074, in All.lean's order), so simulations need no prjxray-db decode.
usage: lean2json.py NETPS_DIR OUT.json"""
import re, sys, glob, json, os
D = sys.argv[1]
s = open(os.path.join(D, "Nodes.lean")).read()
lists = re.findall(r'def n(\d+) : List String := \[(.*?)\]\n', s, re.S)
nodes = []
for _, body in sorted(lists, key=lambda x: int(x[0])):
    nodes += json.loads("[" + body + "]")
P = re.compile(r'P "((?:[^"\\]|\\.)*)" (\d+) (\d+) (\d+) (\d+) (\d+) (\d+)')
G = re.compile(r'⟨"((?:[^"\\]|\\.)*)", (\d+), (\d+), \[([^\]]*)\], \[(.*?)\], (\d+)⟩[,\]]?\s*$')
A = re.compile(r'⟨(\d+), (\d+), (\d+), (\d+)⟩')
gates = []
for f in sorted(glob.glob(os.path.join(D, "G*.lean"))):
    for l in open(f):
        l = l.strip()
        m = P.match(l)
        if m:
            n, i, o, a, b, c, d = m.groups()
            gates.append(dict(name=json.loads('"%s"' % n), k=1, init=2, ins=[int(i)], arcs=[dict(fmin=int(a), fmax=int(b), smin=int(c), smax=int(d))], out=int(o)))
            continue
        m = G.match(l)
        if m:
            n, k, init, ins, arcs, o = m.groups()
            gates.append(dict(name=json.loads('"%s"' % n), k=int(k), init=int(init),
                              ins=[int(x) for x in ins.split(",")] if ins.strip() else [],
                              arcs=[dict(fmin=int(a), fmax=int(b), smin=int(c), smax=int(d)) for a, b, c, d in A.findall(arcs)],
                              out=int(o)))
print(len(nodes), "nodes", len(gates), "gates", file=sys.stderr)
json.dump(dict(nodes=nodes, gates=gates), open(sys.argv[2], "w"))
