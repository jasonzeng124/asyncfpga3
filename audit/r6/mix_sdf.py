#!/usr/bin/env python3
"""mix_sdf.py BASE_SDF HI_SDF ARCLIST OUT_SDF: copy BASE_SDF, but every arc listed in ARCLIST (src\tdst) takes
HI_SDF's first-column value in all fields (single-valued corner SDFs from audit/tc/corner_sdf.py)."""
import sys, re
base, hi, lst, out = sys.argv[1:5]
un = lambda s: s.replace("\\", "")
RI = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RO = re.compile(r"^(\s*\(IOPATH\s+(\S+)\s+(\S+)\s+)\((-?\d+):(-?\d+):(-?\d+)\)\s*\((-?\d+):(-?\d+):(-?\d+)\)(.*)$")
RC = re.compile(r"^(\s*\(INTERCONNECT\s+(\S+)\s+(\S+)\s+)\((-?\d+):(-?\d+):(-?\d+)\)\s*\((-?\d+):(-?\d+):(-?\d+)\)(.*)$")
def scan(p):
    L = open(p).read().splitlines(); inst = None; K = {}
    for i, l in enumerate(L):
        m = RI.search(l)
        if m: inst = un(m.group(1)); continue
        m = RC.match(l)
        if m: K[(un(m.group(2)), un(m.group(3)))] = (i, m); continue
        m = RO.match(l)
        if m and inst: K[(f"{inst}/{un(m.group(2))}", f"{inst}/{un(m.group(3))}")] = (i, m)
    return L, K
L, KB = scan(base); _, KH = scan(hi)
want = {tuple(l.rstrip("\n").split("\t")[:2]) for l in open(lst)}
n = 0
for k in want:
    if k in KB and k in KH:
        i, m = KB[k]; v = int(KH[k][1].group(4))
        L[i] = f"{m.group(1)}({v}:{v}:{v}) ({v}:{v}:{v}){m.group(10)}"; n += 1
print(f"{n} of {len(want)} arcs raised")
open(out, "w").write("\n".join(L) + "\n")
