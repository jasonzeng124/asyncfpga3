#!/usr/bin/env python3
"""Shard C quiet study (UNTRUSTED). One settle_partial instance for the whole exact set at reset:
members = every exact gate node + the k=0 constant gates they force through; root = rst only (held on [0,R)).
rho(w) = 0 if every forcing source is the root, else 1 + max rho over member forcing sources.
Writes reset_island.txt: node, value, forcing pins, rho, kind."""
import pickle, collections
import tern
from common import *
C = tern.C; g = C['gates']; names = C['names']
I2 = pickle.load(open("/tmp/claude-0/quiet/island2.pkl", "rb")); val = I2['val']; ps = dict(I2['ps'])
rst = tern.bs['rst']
consts = {g[n]['pins'][j]['src'] for n in ps for j in ps[n] if g.get(g[n]['pins'][j]['src'], {}).get('k', -1) == 0}
for c in consts: ps[c] = []
rho = {}
def r(n):
    if n in rho: return rho[n]
    s = [g[n]['pins'][j]['src'] for j in ps[n]]
    s = [x for x in s if x != rst]
    rho[n] = 0 if not s else 1 + max(r(x) for x in s); return rho[n]
for n in ps: r(n)
kind = lambda n: 'const' if n in consts else ('reset' if n in tern.R else ('arb' if n in C['CTRL'] else 'comb'))
print("members %d (exact gates %d + constant gates %d); root: rst only" % (len(ps), len(ps) - len(consts), len(consts)))
print("rho max %d; by kind %s" % (max(rho.values()), {k: max(rho[n] for n in ps if kind(n) == k) for k in ('const', 'reset', 'arb', 'comb')}))
print("rho histogram", sorted(collections.Counter(rho.values()).items()))
I = island_list()
print("Lean island members all in this set with same value (0):", all(n in ps and val[n] == 0 for n in I if n not in tern.HELD))
with open("/tmp/claude-0/quiet/reset_island.txt", "w") as f:
    for n in sorted(ps):
        f.write("%d %d %s %d %s %s\n" % (n, val[n], ",".join(map(str, ps[n])) or "-", rho[n], kind(n), names[n]))
print("wrote reset_island.txt")
