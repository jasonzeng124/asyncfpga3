#!/usr/bin/env python3
"""Shard C quiet study (UNTRUSTED). Ternary/stability fixpoint of THE target's collapsed cone under reset:
rst=1, req=0, out0.ack=0, pend.ack=0, operand buses unknown and moving. Status per node:
('K',v) value forced; ('C',None) constant but value not determined (holds); ('V',None) may move.
Also question 1 (b): settle_PS-style coverage (every transitive non-comb feeder of a comb node, over ALL pins,
is in resetList / a constant gate / a held env node)."""
import itertools, collections, pickle, sys
from common import *

C = classify.load(); g = C['gates']; names = C['names']; bs = C['bs']
HELD = {bs['rst']: 1, bs['req']: 0, bs['out0_ack']: 0, bs['pend_ack']: 0}
R = reset_list()

def tern(init, k, vals):
    """vals: list of 0/1/None; return 0/1 or None (X)"""
    xs = [j for j in range(k) if vals[j] is None]
    base = sum(1 << j for j in range(k) if vals[j] == 1)
    out = None
    for bits in itertools.product((0, 1), repeat=len(xs)):
        a = base | sum(1 << j for j, b in zip(xs, bits) if b)
        o = (init >> a) & 1
        if out is None: out = o
        elif out != o: return None
    return out

def evalgate(n, st):
    G = g[n]; k = G['k']; I = G['init']
    if k == 0: return ('K', I & 1)
    pins = [p['src'] for p in G['pins']]
    selfp = [j for j, s in enumerate(pins) if s == n and G['pins'][j]['live']]
    cpins = sorted({s for j, s in enumerate(pins) if s != n and st[s][0] == 'C'})
    if len(cpins) > 10: return ('V', None)
    res = []
    for asg in itertools.product((0, 1), repeat=len(cpins)):
        A = dict(zip(cpins, asg))
        def val(j, selfb=None):
            s = pins[j]
            if s == n and selfp: return selfb
            t = st[s]
            if t[0] == 'K': return t[1]
            if t[0] == 'C': return A[s]
            return None
        if not selfp:
            o = tern(I, k, [val(j) for j in range(k)])
            if o is None: return ('V', None)
            res.append(('f', o))
        else:
            o0 = tern(I, k, [val(j, 0) for j in range(k)])
            o1 = tern(I, k, [val(j, 1) for j in range(k)])
            if o0 is None or o1 is None: return ('V', None)
            if o0 == 1 and o1 == 0: return ('V', 'osc')
            res.append(('f', o0) if o0 == o1 else ('h', None))
    if all(r[0] == 'f' for r in res) and len({r[1] for r in res}) == 1: return ('K', res[0][1])
    return ('C', None)

def fixpoint(over=None):
    st = collections.defaultdict(lambda: ('V', None))
    for e, v in HELD.items(): st[e] = ('K', v)
    if over:
        for n, v in over.items(): st[n] = ('K', v)
    rounds = 0
    while True:
        rounds += 1; ch = 0
        for n in g:
            if over and n in over: continue
            r = evalgate(n, st)
            old = st[n]
            # monotone promotion only: V -> C -> K
            rank = {'V': 0, 'C': 1, 'K': 2}
            if rank[r[0]] > rank[old[0]]:
                st[n] = r; ch += 1
        if not ch: break
    return st, rounds

if __name__ == "__main__":
    EX = C['EXACT']; comb = C['comb']; const = C['const']
    # ---- Q1 (a), (b) ----
    a = {n for n in EX if n in R}
    root_ok = lambda s: s in R or s in const or s in HELD
    good = {}
    def gd(n):
        if n in good: return good[n]
        if n not in comb: good[n] = root_ok(n); return good[n]
        good[n] = None
        r = all(gd(p['src']) for p in g[n]['pins'])
        good[n] = r; return r
    sys.setrecursionlimit(100000)
    b = {n for n in EX if n in comb and gd(n)}
    hs = {n for n in EX if n in HELD}
    # live-pin variant
    goodL = {}
    def gdL(n):
        if n in goodL: return goodL[n]
        if n not in comb: goodL[n] = root_ok(n); return goodL[n]
        goodL[n] = None
        r = all(gdL(p['src']) for p in C['live'][n]); goodL[n] = r; return r
    bL = {n for n in EX if n in comb and gdL(n)}
    c = EX - a - b - hs
    print("EXACT %d: (a) in resetList %d; (b) comb, all-pin roots in resetList/const/held env %d (live pins only: %d);"
          " held env %d; (c) rest %d" % (len(EX), len(a), len(b), len(bL), len(hs), len(c)))
    cst = collections.Counter('stor' if n in C['stor'] else ('comb' if n in comb else 'other') for n in c)
    print("(c) kinds:", dict(cst))
    # what blocks the comb (c) nodes: the non-comb roots that are not ok
    blk = collections.Counter(); blkn = collections.defaultdict(set)
    for n in c:
        if n not in comb: continue
        seen = set(); todo = [n]
        while todo:
            u = todo.pop()
            for p in g[u]['pins']:
                s = p['src']
                if s in seen: continue
                seen.add(s)
                if s in comb: todo.append(s)
                elif not root_ok(s): blkn[n].add(s)
    rootc = collections.Counter(s for n in blkn for s in blkn[n])
    def kind(s):
        if s in C['LATCH']: return 'data latch'
        if s in C['CTRL']: return 'ctrl stor (not reset)'
        if s in C['data_env']: return 'env data'
        if s in C['ENV']: return 'env'
        return '?'
    print("blocking roots of (c)-comb nodes:", len(rootc), collections.Counter(kind(s) for s in rootc))
    for s, k in rootc.most_common():
        print("   root %6d %-18s %-22s blocks %d exact comb nodes" % (s, names[s], kind(s), k))
    # ---- Q2 ternary ----
    st, rounds = fixpoint()
    print("fixpoint rounds", rounds)
    cnt = collections.Counter(st[n][0] for n in EX)
    print("EXACT status under reset:", dict(cnt))
    print("(c) status:", collections.Counter(st[n][0] for n in c))
    print("(b) status:", collections.Counter(st[n][0] for n in b), "(a):", collections.Counter((st[n][0], st[n][1] == int(R[n][1])) for n in a))
    for n in sorted(EX):
        if st[n][0] != 'K':
            print("  not forced: %6d %-18s %-5s %s" % (n, names[n], 'stor' if n in C['stor'] else 'comb', st[n]))
    pickle.dump(dict(a=a, b=b, bL=bL, c=c, hs=hs, st=dict(st), blkn=dict(blkn)), open("/tmp/claude-0/quiet/q.pkl", "wb"))
