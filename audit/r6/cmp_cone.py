#!/usr/bin/env python3
"""Compare two SDFs (first column) on the arcs listed in adv_arcs.txt (+ request arcs if given): sums and biggest diffs.
   cmp_cone.py SDF_A SDF_B ARCLIST"""
import sys, re
un = lambda s: s.replace("\\", "")
RI = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RO = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((-?\d+)")
RC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((-?\d+)")
def load(p):
    d, inst = {}, None
    for l in open(p):
        m = RI.search(l)
        if m: inst = un(m.group(1)); continue
        m = RC.search(l)
        if m: d[(un(m.group(1)), un(m.group(2)))] = int(m.group(3)); continue
        m = RO.search(l)
        if m and inst: d[(f"{inst}/{un(m.group(1))}", f"{inst}/{un(m.group(2))}")] = int(m.group(3))
    return d
A, B = load(sys.argv[1]), load(sys.argv[2])
arcs = [tuple(l.split("\t")[:2]) for l in open(sys.argv[3])]
diffs = [(B.get(k, 0) - A.get(k, 0), k, A.get(k), B.get(k)) for k in arcs]
print("arcs", len(arcs), "missing in A", sum(1 for k in arcs if k not in A), "missing in B", sum(1 for k in arcs if k not in B))
diffs.sort()
for x in diffs[:12] + diffs[-12:]: print(x)
