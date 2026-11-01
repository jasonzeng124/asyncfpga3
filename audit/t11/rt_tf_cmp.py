#!/usr/bin/env python3
"""rt_tf_cmp.py (audit T11): is the Lean round trip's target feature list `tf` (FormalWit/RT/F00..F63.lean leaves,
in leaf order) exactly the auditor's own canonical read-back of the target .bit?
    python3 -I rt_tf_cmp.py RT_DIR OWN_CANONICAL.fasm
Own parse; canonical FASM writes INIT bit 0 without an index, so 'xLUT.INIT' is read as 'xLUT.INIT[0]'."""
import re, sys, collections
d, own = sys.argv[1:3]
leaves = []
for i in range(64):
    s = open("%s/F%02d.lean" % (d, i)).read()
    leaves += [(m.group(1), int(m.group(2))) for m in re.finditer(r'\.leaf "((?:[^"\\]|\\.)*)" (\d+)\)', s)]
L = [f for f, _ in leaves]
print("Lean leaves", len(L), "; leaf indices = 0..n-1 in order:", [j for _, j in leaves] == list(range(len(L))), "; sorted:", L == sorted(L))
O = []
for l in open(own):
    t = l.split("#", 1)[0].strip()
    if t:
        O.append(t + "[0]" if re.search(r"\.[A-D]LUT\.INIT$", t) else t)
print("own canonical read-back", len(O), "distinct", len(set(O)))
cl, co = collections.Counter(L), collections.Counter(O)
print("tf == own read-back (as multisets):", cl == co, "; Lean-only", sum((cl - co).values()), "; own-only", sum((co - cl).values()))
for x in list((cl - co).items())[:5] + list((co - cl).items())[:5]:
    print("   ", x)
