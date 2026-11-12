#!/usr/bin/env python3
"""Shard C quiet study (UNTRUSTED). Can every exact node be forced at reset by an island-style certificate
(ForcesP on a pin subset, values in {0,1}, forcing sources = exact nodes, held env (rst=1, req=0, out0.ack=0,
pend.ack=0) or k=0 constant gates)? Data nodes are forbidden as forcing sources. Greedy minimal forcing sets.
Reports: coverage, comb rank depth, storage members not in resetList, use of const (VCC) pins, values = 1."""
import itertools, collections, pickle
import tern
from common import *
C = tern.C; g = C['gates']; names = C['names']; R = tern.R
EX = C['EXACT']; HELD = tern.HELD
val = {e: v for e, v in HELD.items()}
for n in g:
    if g[n]['k'] == 0: val[n] = g[n]['init'] & 1
def forces(n, asg):
    G = g[n]; k = G['k']; v = [None] * k
    for j, b in asg: v[j] = b
    return tern.tern(G['init'], k, v)
order = []; ps = {}
changed = True; rnd = 0
while changed:
    changed = False; rnd += 1; new = {}
    for n in EX:
        if n in val or n not in g: continue
        G = g[n]; pins = [p['src'] for p in G['pins']]
        cand = [(j, val[s]) for j, s in enumerate(pins) if s in val and s != n]
        o = forces(n, cand)
        if o is None: continue
        # greedy minimise
        cur = list(cand)
        for e in list(cand):
            t = [x for x in cur if x != e]
            if forces(n, t) == o: cur = t
        new[n] = (o, [j for j, _ in cur])
    for n, (o, js) in new.items():
        val[n] = o; ps[n] = js; changed = True; order.append((rnd, n))
cov = {n for n in EX if n in val}
print("exact covered with data forbidden: %d / %d (rounds %d)" % (len(cov), len(EX), rnd))
miss = EX - cov
for n in sorted(miss)[:30]: print("  missing", n, names[n])
stor_nr = [n for n in ps if n in C['stor'] and n not in R]
print("storage members not in resetList:", len(stor_nr), stor_nr)
constuse = {n for n in ps for j in ps[n] if g.get(g[n]['pins'][j]['src'], {}).get('k', -1) == 0}
print("members whose forcing set uses a k=0 constant gate:", len(constuse), "(of which stor %d)" % len(constuse & C['stor']))
envuse = collections.Counter(names[g[n]['pins'][j]['src']] for n in ps for j in ps[n] if g[n]['pins'][j]['src'] in HELD)
print("forcing pins from held env:", dict(envuse))
ones = sorted(n for n in EX if val.get(n) == 1)
print("exact nodes valued 1: %d: %s" % (len(ones), [(n, names[n], 'stor' if n in C['stor'] else 'comb') for n in ones]))
# reset-list members: does the forcing set equal the reset pin alone?
rl_other = [n for n in ps if n in R and [g[n]['pins'][j]['src'] for j in ps[n]] != [tern.bs['rst']]]
print("resetList members whose greedy forcing set is not just the reset pin:", len(rl_other))
# combinational rank within the comb members (storage + env + const as roots)
rk = {}
def rank(n):
    if n in rk: return rk[n]
    if n not in C['comb'] or n not in ps: rk[n] = -1; return -1
    rk[n] = 1 + max([rank(g[n]['pins'][j]['src']) for j in ps[n]] + [-1]); return rk[n]
import sys; sys.setrecursionlimit(100000)
mr = max(rank(n) for n in ps)
print("max comb rank in the reset island (comb above storage roots): %d" % mr)
# compare with Lean rkPS? (global rank not available here) -- report storage-through depth
dep = {}
for r_, n in order: dep[n] = r_
print("max forcing round:", max(dep.values()), "; rounds of the 9 arbiter states:", sorted({dep[n] for n in stor_nr}))
pickle.dump(dict(val=val, ps=ps, order=order), open("/tmp/claude-0/quiet/island2.pkl", "wb"))
