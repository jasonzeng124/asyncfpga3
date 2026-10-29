#!/usr/bin/env python3
"""Negative control SDF edit: for one SDF INSTANCE, set the hold value of its
(posedge D)/(negedge D) SETUPHOLD lines to NEWHOLD, leave everything else.
usage: nc_edit.py in.sdf out.sdf '<sdf instance text>' NEWHOLD"""
import sys
src, dst, inst, newhold = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
lines = open(src).read().split('\n')
inside = False; n = 0
for i, l in enumerate(lines):
    s = l.strip()
    if s.startswith('(INSTANCE '):
        inside = (s[len('(INSTANCE '):-1] == inst)
    if inside and s.startswith('(SETUPHOLD (posedge D)') or inside and s.startswith('(SETUPHOLD (negedge D)'):
        head, tail = l.rsplit('(', 1)
        lines[i] = f'{head}({newhold}:{newhold}:{newhold}))'
        n += 1; print('edited:', lines[i].strip())
open(dst, 'w').write('\n'.join(lines))
assert n == 2, n
