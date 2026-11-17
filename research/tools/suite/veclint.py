#!/usr/bin/env python3
"""veclint.py VEC.hex VEC.exp -- the suite's vector rules (kernels/SUITE.md), checked, exit 1 on any breach:
bench format (two 8-digit hex words per line, at most 256 vectors: cells/gls/ps/ps7_bench.v's vmem), one expected
8-digit word per vector, no two consecutive expected values equal (a result stream one call behind must not pass),
and not mostly 0 (at most a quarter of the answers 0, the value a dead datapath most often returns)."""
import re, sys
vec = [l.split() for l in open(sys.argv[1]).read().splitlines() if l.strip()]
exp = [l.strip() for l in open(sys.argv[2]).read().splitlines() if l.strip()]
bad = []
if len(vec) > 256: bad.append("%d vectors: the bench reads at most 256" % len(vec))
for i, w in enumerate(vec):
    if len(w) != 2 or not all(re.fullmatch(r"[0-9a-f]{8}", x) for x in w): bad.append("vector %d not two 8-digit hex words: %r" % (i, w))
if len(exp) != len(vec): bad.append("%d expected values for %d vectors" % (len(exp), len(vec)))
for i, e in enumerate(exp):
    if not re.fullmatch(r"[0-9a-f]{8}", e): bad.append("expected %d is not an 8-digit hex word: %r" % (i, e))
for i in range(1, len(exp)):
    if exp[i] == exp[i - 1]: bad.append("expected %d equals expected %d (%s): one call behind would pass" % (i, i - 1, exp[i]))
z = sum(e == "00000000" for e in exp)
if 4 * z > len(exp): bad.append("%d of %d expected values are 0" % (z, len(exp)))
for b in bad: print("veclint: " + b)
print("veclint: %s %d vectors, %d distinct answers, %d zero%s" % ("FAIL" if bad else "ok", len(vec), len(set(exp)), z,
      "" if z == 1 else "s"))
sys.exit(1 if bad else 0)
