#!/usr/bin/env python3
"""shmask_patch.py TOOLSCOPY -- runtime patch to a COPY of dfimport/mlir2lean.py, applied when the caller exports
BDC_SHIFT_MASK=1 (the build knob itself; shard A, 2026-11-22, FOR-RESEARCH A36/A37). It mirrors bdc/compute.py's
binary_expr at research 196de620f1: for shli / shrui / shrsi of width w > 1 whose amount is NOT a literal (a fused
region's constant stays unmasked, as in bdc), the amount b becomes (b & (2^k - 1)) with k = (w - 1).bit_length(),
an andi of width w. Lean's Ops.shli / shrui / shrsi are unchanged; the graph simply computes on the masked amount.
Also (if the opsx patch is applied) one proof step in auto_ops2_pre: `simp (disch := omega) only [Nat.mod_eq_of_lt]`,
which drops a `% 2^k` that omega shows is below its modulus (the masked amount equals the raw one when it is < w).
SHMASK_CONTROL_MASK=m (negative control ONLY): mask with m instead of 2^k - 1."""
import sys, os
T = sys.argv[1]
a = os.path.join(T, 'dfimport', 'mlir2lean.py'); s = open(a).read()
old = '        return ("bin", op, self.em.width(n.results[0]), ports["a"], ports["b"])\n'
assert s.count(old) == 1
new = '''        b = ports["b"]
        if op in ("shli", "shrui", "shrsi") and self.em.width(n.results[0]) > 1 and b[0] != "lit":
            wr = self.em.width(n.results[0])
            b = ("bin", "andi", wr, b, ("lit", int(os.environ.get("SHMASK_CONTROL_MASK", (1 << (wr - 1).bit_length()) - 1))))
        return ("bin", op, self.em.width(n.results[0]), ports["a"], b)
'''
s = s.replace(old, new)
open(a, 'w').write(s)
ap = os.path.join(T, 'autoproof', 'autoproof.py'); t = open(ap).read()
k = "\\n  try simp only [Ops.extsi, "   # the second line of auto_ops2_pre (opsx), in autoproof's escaped string
if t.count(k) == 1:
    t = t.replace(k, "\\n  try simp (disch := omega) only [Nat.mod_eq_of_lt] at *" + k)
    open(ap, 'w').write(t)
