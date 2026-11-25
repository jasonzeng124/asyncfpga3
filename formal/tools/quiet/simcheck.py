#!/usr/bin/env python3
"""Shard C quiet study (UNTRUSTED). Cross-check reset_island.txt values against tocc's transport simulation
(hist_c0/c1.pkl, all nodes start at 0 in sim): exact node value at R-1, and last change before R."""
import pickle
import tern
C = tern.C; EX = C['EXACT']
val = {}
for l in open("/tmp/claude-0/quiet/reset_island.txt"):
    a = l.split(); val[int(a[0])] = int(a[1])
for e, v in tern.HELD.items(): val[e] = v
for c in (0, 1):
    h = pickle.load(open("/tmp/claude-0/tocc/hist_c%d.pkl" % c, "rb")); R = h['R']; H = h['hist']
    def at(n, t):
        v0, fl = H.get(n, (0, []))
        k = sum(1 for x in fl if x <= t); return (v0 + k) % 2 if isinstance(v0, int) else (int(v0) ^ (k & 1))
    bad = [n for n in EX if at(n, R - 1) != val[n]]
    last = max((max([x for x in H.get(n, (0, []))[1] if x < R] or [0]), n) for n in EX if n != tern.bs['rst'])
    print("corner %d: R=%d, exact nodes disagreeing with reset_island at R-1: %d %s; last exact change before R at %d (node %d)" % (
        c, R, len(bad), bad[:10], last[0], last[1]))
