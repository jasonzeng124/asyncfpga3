#!/usr/bin/env python3
"""dec_patch.py TOOLSCOPY -- runtime patch to a COPY of autoproof.py (AP_DEC=1, shard A 2026-11-20): every C variable v
also offers the candidate template expression `v + 0xFFFFFFFF` (= v - 1 mod 2^32) when autoproof guesses which C
expression a graph variable carries. Needed for graphs whose loop ring carries n - 1 (ring_dec_route.py's plain move).
Only adds candidates: each one is still checked against every observation and then by Lean."""
import os, sys
a = os.path.join(sys.argv[1], 'autoproof', 'autoproof.py'); s = open(a).read()
old = '        cands = [("var", i) for i in range(len(P.vars))]\n'
new = old + ('        if __import__("os").environ.get("AP_DEC") == "1":\n'
             '            cands += [("bin", "addi", 32, ("var", i), ("lit", 4294967295)) for i in range(len(P.vars))]\n')
assert old in s, 'dec_patch: anchor not found'
s = s.replace(old, new, 1)
open(a, 'w').write(s)
