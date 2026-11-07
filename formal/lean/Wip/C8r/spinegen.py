#!/usr/bin/env python3
"""C-8r: the circuit spine of gcd_hw (which circuit channels carry the control-spine token).

Reads the generated network (Formal/Net/CapstoneNet.lean: chanNames, ops) and GcdHw's
`spine` list, and prints `spL` (one Bool per circuit channel): segment channels `gR.k` of a
GcdHw spine channel R, the joined channel `jL` of a branch whose data input is a spine
channel, and every arbiter output `zR` / `accR`. Whether this set is a valid spine is NOT
trusted: `CapstoneCutSpine.lean` checks the shape conditions over all operators by kernel
evaluation. Usage: spinegen.py [out.lean]
"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
NET = os.path.join(HERE, "..", "..", "Formal", "Net")
net = open(os.path.join(NET, "CapstoneNet.lean")).read()
gh = open(os.path.join(NET, "GcdHw.lean")).read()
names = re.findall(r'"([^"]*)"', re.search(r"def chanNames : List String := \[(.*?)\]\n", net).group(1))
spine = {int(x) for x in re.search(r"def spine : List Nat := \[(.*?)\]", gh).group(1).split(",")}
ops = re.search(r"def ops : List \(K NC\) := \[\n(.*?)\n\]", net, re.S).group(1).split("\n")
bj = {}
for o in ops:
    m = re.match(r"\s*K\.bjoin \[(\d+), (\d+)\] (\d+)", o)
    if m: bj[int(m.group(3))] = int(m.group(2))
sp = [False] * len(names)
for c, n in enumerate(names):
    m = re.fullmatch(r"g(\d+)\.\d+", n)
    if m and int(m.group(1)) in spine: sp[c] = True
    if n.startswith("z") or n.startswith("acc"): sp[c] = True
for c, n in enumerate(names):
    if n.startswith("j") and sp[bj[c]]: sp[c] = True
txt = "[" + ", ".join("true" if b else "false" for b in sp) + "]"
print(f"-- {sum(sp)} spine channels of {len(sp)}", file=sys.stderr)
print(txt)
