#!/usr/bin/env python3
"""shmask_patch.py TOOLSCOPY -- runtime patch to a COPY of dfimport/mlir2lean.py, applied when the caller exports
BDC_SHIFT_MASK=1 (the build knob itself; shard A, 2026-11-22, FOR-RESEARCH A36/A37). It mirrors bdc/compute.py's
binary_expr at research 196de620f1: for shli / shrui / shrsi of width w > 1 whose amount is NOT a literal (a fused
region's constant stays unmasked, as in bdc), the amount b becomes (b & (2^k - 1)) with k = (w - 1).bit_length(),
an andi of width w. Lean's Ops.shli / shrui / shrsi are unchanged; the graph simply computes on the masked amount."""
import sys, os
T = sys.argv[1]
a = os.path.join(T, 'dfimport', 'mlir2lean.py'); s = open(a).read()
old = '        return ("bin", op, self.em.width(n.results[0]), ports["a"], ports["b"])\n'
assert s.count(old) == 1
new = '''        b = ports["b"]
        if op in ("shli", "shrui", "shrsi") and self.em.width(n.results[0]) > 1 and b[0] != "lit":
            wr = self.em.width(n.results[0])
            b = ("bin", "andi", wr, b, ("lit", (1 << (wr - 1).bit_length()) - 1))
        return ("bin", op, self.em.width(n.results[0]), ports["a"], b)
'''
s = s.replace(old, new)
open(a, 'w').write(s)
