#!/usr/bin/env python3
"""Shard C quiet study (UNTRUSTED). Synchronous (Jacobi) version of tern.py's fixpoint: depth d(n) = first round
at which n is forced (K). Comb depth ~ settle steps (each costs <= M), storage steps cost one pin delay too.
Also: (c) node details (forcing pins, values), the 9 arbiter states, and island coverage of the exact nodes."""
import pickle, collections
from common import *
import tern
C = tern.C; g = C['gates']; names = C['names']
Q = pickle.load(open("/tmp/claude-0/quiet/q.pkl", "rb"))
st = collections.defaultdict(lambda: ('V', None))
for e, v in tern.HELD.items(): st[e] = ('K', v)
depth = {e: 0 for e in tern.HELD}
for n in g:
    if g[n]['k'] == 0: st[n] = ('K', g[n]['init'] & 1); depth[n] = 0
rank = {'V': 0, 'C': 1, 'K': 2}
r = 0
while True:
    r += 1
    new = {}
    for n in g:
        if st[n][0] == 'K': continue
        o = tern.evalgate(n, st)
        if rank[o[0]] > rank[st[n][0]]: new[n] = o
    if not new: break
    for n, o in new.items():
        st[n] = o
        if o[0] == 'K': depth[n] = r
EX = C['EXACT']
print("Jacobi rounds", r, "; exact all K:", all(st[n][0] == 'K' for n in EX))
print("all-gate status:", collections.Counter(st[n][0] for n in g))
dE = [depth[n] for n in EX]
print("exact depth max %d; histogram (by 10s) %s" % (max(dE), sorted(collections.Counter(d // 10 * 10 for d in dE).items())))
for nm, S in (("a", Q['a']), ("b", Q['b']), ("c", Q['c'])):
    print("  (%s) max depth %d" % (nm, max(depth[n] for n in S)))
# comb-only depth from storage: count only comb levels after last storage
# (c) details
R = reset_list()
def pinfo(n):
    out = []
    for j, p in enumerate(g[n]['pins']):
        s = p['src']; t = st[s]
        out.append("%d:%s=%s%s" % (j, s, t[1] if t[0] == 'K' else t[0], "" if p['live'] else "(dead)"))
    return " ".join(out)
print("\nthe 9 control storage nodes not in resetList (arbiter states):")
arbs = sorted(n for n in Q['c'] if n in C['stor'])
for n in arbs:
    G = g[n]
    # does reset alone force it?
    rj = [j for j, p in enumerate(G['pins']) if p['src'] == tern.bs['rst']][0]
    alone = tern.tern(G['init'], G['k'], [1 if j == rj else None for j in range(G['k'])])
    print("  %6d %-16s INIT %s -> %s at depth %d; reset alone forces: %s; pins %s" % (
        n, names[n], hex(G['init']), st[n][1], depth[n], alone, pinfo(n)))
# which nodes force the 9: show for each the minimal pins needed (pins whose K value is needed)
print("\n(c) comb nodes: 232; depth max", max(depth[n] for n in Q['c'] if n not in C['stor']))
# island coverage
I = island_list()
Ik = set(I)
print("\nisland members %d; in EXACT %d; in DATA %d; not in model %d" % (len(Ik), len(Ik & EX), len(Ik & C['DATA']), len(Ik - set(g) - set(C['ENV']))))
print("island values agree with ternary:", all(st[n] == ('K', 0) for n in Ik if n in g))
print("exact not in island: %d  ((a) %d, (b) %d, (c) %d, held env %d)" % (len(EX - Ik), len(Q['a'] - Ik), len(Q['b'] - Ik), len(Q['c'] - Ik), len(Q['hs'] - Ik)))
print("exact values: K0 %d K1 %d" % (sum(st[n] == ('K', 0) for n in EX), sum(st[n] == ('K', 1) for n in EX)))
pickle.dump(dict(st=dict(st), depth=depth), open("/tmp/claude-0/quiet/depth.pkl", "wb"))
