#!/usr/bin/env python3
"""Shard C quiet study (UNTRUSTED). Breakdown of the 232 (c) comb exact nodes by blocker kind, with examples."""
import pickle, collections
import tern
C = tern.C; g = C['gates']; names = C['names']
Q = pickle.load(open("/tmp/claude-0/quiet/q.pkl", "rb")); I2 = pickle.load(open("/tmp/claude-0/quiet/island2.pkl", "rb"))
arbs = {n for n in C['CTRL'] if n not in tern.R}
cat = collections.Counter(); ex = {}
for n, bl in Q['blkn'].items():
    k = ('arb' if bl & arbs else '') + ('+latch' if bl - arbs else '')
    cat[k] += 1; ex.setdefault(k, n)
print("(c) comb by blocker:", dict(cat))
for k, n in ex.items():
    G = g[n]; v = I2['val'][n]
    print("  e.g. %s: %d %s val %d; forcing pins %s; data-latch pins (dead under forcing): %s" % (
        k, n, names[n], v, [(G['pins'][j]['src'], I2['val'][G['pins'][j]['src']]) for j in I2['ps'][n]],
        [p['src'] for p in G['pins'] if p['src'] in C['LATCH']]))
dl = {s for bl in Q['blkn'].values() for s in bl if s in C['LATCH']}
direct = {p['src'] for n in Q['c'] if n in g for p in g[n]['pins'] if p['src'] in C['LATCH']}
print("data latches in the all-pin cone of (c) nodes: %d; read directly by an exact gate: %d" % (len(dl), len(direct)))
