#!/usr/bin/env python3
"""Shard C quiet study (UNTRUSTED). (1) Global comb rank (longest comb path over ALL pins, as rkPS/comb_ranked)
of the exact comb nodes, cone-local (the cone is closed under fan-in, so it should equal rkPS); spot-check
against the island's Lean bound (members' rank <= 85). (2) Re-run island2's forcing with ONLY rst held
(requests and acks free): is the exact reset state still determined?"""
import sys, collections, pickle
import tern
from common import *
C = tern.C; g = C['gates']; comb = C['comb']; names = C['names']
sys.setrecursionlimit(100000)
rk = {}
def rank(n):
    if n in rk: return rk[n]
    if n not in comb: return -1
    rk[n] = 0
    rk[n] = 1 + max([rank(p['src']) for p in g[n]['pins']] + [-1]) if g[n]['pins'] else 0
    return rk[n]
# Lean rank convention: comb node with no comb sources has rank 0
for n in comb: rank(n)
EXc = [n for n in C['EXACT'] if n in comb]
print("global comb rank: max over all comb %d; over exact comb %d" % (max(rk.values()), max(rk[n] for n in EXc)))
print("exact comb rank histogram (by 10):", sorted(collections.Counter(rk[n] // 10 * 10 for n in EXc).items()))
I = island_list()
print("island comb members max rank (model):", max(rk[n] for n in I if n in comb), "(Lean check: <= 85)")
for b in (104695, 160957): print("  rank", b, rk[b], "(Lean ranks_out: 7, 18)")
# (2) only rst
I2 = pickle.load(open("/tmp/claude-0/quiet/island2.pkl", "rb"))
used = collections.Counter()
for n, js in I2['ps'].items():
    for j in js: used[g[n]['pins'][j]['src']] += 0
srcs_needed = {g[n]['pins'][j]['src'] for n, js in I2['ps'].items() for j in js}
print("held env nodes used as forcing sources:", [names[s] for s in srcs_needed if s in tern.HELD])
nonex = [s for s in srcs_needed if s not in C['EXACT'] and not (s in g and g[s]['k'] == 0)]
print("forcing sources outside EXACT and not constant:", nonex)
