#!/usr/bin/env python3
"""Find the signed-compare chain of a generated unit (Formal/Gen/Compute/GcdD/<U>.lean) and print
the `SGrp` list for `SltOK` (untrusted: Lean checks the certificate by decide)."""
import re, sys
src = open(sys.argv[1]).read()
cells = re.findall(r"^  (\.(?:lut|muxf|inv|carry4).*?)(?:,)?$", src, re.M)
c4 = []
for idx, c in enumerate(cells):
    if c.startswith(".carry4"):
        m = re.match(r"\.carry4 \((.*?)\) \((.*?)\) \[(.*?)\] \[(.*?)\] (.*)$", c)
        di = [x.strip() for x in m.group(3).split(",")]; s = [x.strip() for x in m.group(4).split(",")]
        outs = m.group(5).split()
        c4.append((idx, m.group(1), di, s, outs))
# LUT inputs by output net
lutin = {}
for c in cells:
    m = re.match(r"\.lut (\d+) \[(.*?)\] (\d+)$", c)
    if m: lutin[int(m.group(3))] = [x.strip() for x in m.group(2).split(",")]
groups = []
for (idx, ci, di, s, outs) in c4:
    for p in range(4):
        if s[p] == ".c0": continue
        e = int(s[p].split()[1]); d = int(di[p].split()[1])
        bits = sorted(set(int(x.split()[2]) for x in lutin[e] if x.startswith(".inp")))
        groups.append(dict(lo=bits[0], len=len(bits), e=e, d=d, cell=idx, pos=p))
print("[" + ",\n ".join("⟨%d, %d, %d, %d, %d, %d⟩" % (g["lo"], g["len"], g["e"], g["d"], g["cell"], g["pos"]) for g in groups) + "]")
