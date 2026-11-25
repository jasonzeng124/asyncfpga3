#!/usr/bin/env python3
"""Shard C quiet study (UNTRUSTED). Pin-delay bound M (max composite hi over all pins of members) for the reset
island (reset_island.txt) vs the Lean island (islandList), per corner, from model.pkl windows (g=1, kappa=0).
Also the reset-pin arrival (sum max of the rst pin) of storage members."""
import tern
from common import *
C = tern.C; g = C['gates']
mem = [int(l.split()[0]) for l in open("/tmp/claude-0/quiet/reset_island.txt")]
I = [n for n in island_list() if n in g]
for c in (0, 1):
    f = lambda S: max(p['win'][c][1] for n in S for p in g[n]['pins'])
    rs = lambda S: max(p['win'][c][1] for n in S for p in g[n]['pins'] if p['src'] == tern.bs['rst'])
    print("corner %d: M(reset island, %d gates) = %d ps; M(Lean island, %d) = %d ps; max rst-pin arrival: reset island %d, Lean island %d" % (
        c, len(mem), f(mem), len(I), f(I), rs([n for n in mem if n in C['stor']]), rs([n for n in I if n in C['stor']])))
