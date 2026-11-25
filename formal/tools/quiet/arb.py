#!/usr/bin/env python3
"""Shard C quiet study (UNTRUSTED): the 9 arbiter states. Which pin sets force them under reset?
Tests: rst=1 alone; rst=1 + VCC pin (k=0 gate) = 1; minimal forcing pin subsets with the reset-time values."""
import itertools, pickle
import tern
C = tern.C; g = C['gates']; names = C['names']
D = pickle.load(open("/tmp/claude-0/quiet/depth.pkl", "rb")); st = D['st']
arbs = [n for n in C['CTRL'] if n not in tern.R]
for n in sorted(arbs):
    G = g[n]; k = G['k']; I = G['init']; pins = [p['src'] for p in G['pins']]
    rj = pins.index(tern.bs['rst']); vj = [j for j, s in enumerate(pins) if g.get(s, {}).get('k', -1) == 0]
    v = [None] * k; v[rj] = 1
    a1 = tern.tern(I, k, v)
    for j in vj: v[j] = g[pins[j]]['init'] & 1
    a2 = tern.tern(I, k, v)
    # function of the other pins with rst=1, VCC=1: truth table restricted
    print("%6d %s: rst alone -> %s; rst=1 & const pin(s) %s -> %s; other pins %s (resetList? %s)" % (
        n, names[n], a1, [(pins[j], names[pins[j]], g[pins[j]]['init'] & 1) for j in vj], a2,
        [(pins[j], 'self' if pins[j] == n else ('reset-list' if pins[j] in tern.R else ('stor' if pins[j] in C['stor'] else 'comb'))) for j in range(k) if j != rj and j not in vj], False))
    # with rst=0 (after reset), VCC=1: dependence on self (true storage?)
    v0 = [None] * k; v0[rj] = 0
    for j in vj: v0[j] = 1
    selfj = pins.index(n)
    holds = any(tern.tern(I, k, [*(v0[:selfj]), b, *(v0[selfj+1:])]) is None for b in (0, 1))
    print("        after reset the state depends on its other pins / self: %s" % holds)
