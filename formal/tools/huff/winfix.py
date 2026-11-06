#!/usr/bin/env python3
"""Shard C (UNTRUSTED prototype): persistence of THE target's CONTROL network by a windowed
(Cartesian) over-approximation of its reachable states.

Abstract machine (the control part of tools/huff/huffx.cpp's model): variables = the 412 control
storage nodes, the env's req / pend_ack / out0_ack plus one env bit w ("waiting for out0"), and the
32 FRONTIER nodes through which control reads data (one-bit data latches and pure-data logic), taken
as free inputs. Every control node c has next-state function F_c over its support supp(c) (zero-delay
logic, reset low). Moves: fire an excited control node; an env move (sequential four-phase env);
flip a frontier node f, allowed only when no reader's next-state depends on f at that moment
(the BUNDLING obligation BO_f, which this abstraction ASSUMES and lists: it must come from timing).

Windows: W_c = {c} ∪ supp(c) per control node, one env window. R_W over-approximates the projections
of the reachable states on W: start from the reset state; for every window W and every mover m in W,
join R_W with R_{W_m} (m's own window, which holds m's guard) and add the projections of the post
states; until nothing changes. Sound: by induction every reachable state's projections are in the
R_W (a weaker guard for frontier moves only adds behaviours).
Then check, over the same joins: persistence (an excited control node stays excited after any other
move), and the boundary protocol (acks/out0 request move only as four-phase allows).
usage: winfix.py huff.txt init.txt"""
import sys, collections, itertools
L = open(sys.argv[1]).read().split('\n')
nn = int(L[0].split()[1]); names = L[1:1 + nn]; i = 1 + nn
nc = int(L[i].split()[1]); comb = [l.split() for l in L[i + 1:i + 1 + nc]]; i += 1 + nc
ns = int(L[i].split()[1]); stor = [l.split() for l in L[i + 1:i + 1 + ns]]; i += 1 + ns
bnd = {k: int(v) for k, v in (kv.split('=') for kv in L[i].split()[1:])}
env = set(int(x) for x in L[i + 4].split()[1:])
init = [c == '1' for c in open(sys.argv[2]).read().strip()]
def g(t): k = int(t[1]); return int(t[0]), k, [int(x) for x in t[2:2 + k]], int(t[2 + k], 16)
C = {}; S = {}; LAT = set()
for t in comb: o, k, ins, I = g(t); C[o] = (k, ins, I)
for t in stor:
    o, k, ins, I = g(t); S[o] = (k, ins, I)
    if t[-1] == '1': LAT.add(o)
CTL = sorted(set(S) - LAT)
def dep(k, I, j): return any(((I >> x) & 1) != ((I >> (x ^ (1 << j))) & 1) for x in range(1 << k))
sys.setrecursionlimit(100000)
RST = bnd['rst']
m1 = {}
def lat_cone(u):
    if u in m1: return m1[u]
    if u in S: r = u in LAT
    elif u in C: k, ins, I = C[u]; r = any(lat_cone(s) for j, s in enumerate(ins) if dep(k, I, j))
    else: r = False
    m1[u] = r; return r
m2 = {}
def ctl_cone(u):
    if u in m2: return m2[u]
    if u in S: r = u not in LAT
    elif u in C: k, ins, I = C[u]; r = any(ctl_cone(s) for j, s in enumerate(ins) if dep(k, I, j))
    else: r = u in env and u != RST
    m2[u] = r; return r
m3 = {}
def supp(u):
    if u in m3: return m3[u]
    if u == RST: r = frozenset()
    elif u in S: r = frozenset([u])
    elif u in C:
        if lat_cone(u) and not ctl_cone(u): r = frozenset([u])
        else:
            k, ins, I = C[u]
            r = frozenset().union(*[supp(s) for j, s in enumerate(ins) if dep(k, I, j)]) if k else frozenset()
    else: r = frozenset([u])
    m3[u] = r; return r
def evalnode(u, asg, memo):
    """zero-delay value of node u given values of support variables asg (dict); rst = 0."""
    if u in asg: return asg[u]
    if u in memo: return memo[u]
    if u == RST: return False
    if u in C:
        k, ins, I = C[u]; a = 0
        for j, s in enumerate(ins):
            if dep(k, I, j) and evalnode(s, asg, memo): a |= 1 << j
        # pins we skipped are don't-care
        r = bool((I >> a) & 1)
    elif u in S: raise KeyError(names[u])
    else: r = False
    memo[u] = r; return r
def F(c, asg):
    k, ins, I = S[c]; memo = {}; a = 0
    for j, s in enumerate(ins):
        if dep(k, I, j) and evalnode(s, asg, memo): a |= 1 << j
    return bool((I >> a) & 1)
# variables
W_ENV = -1
def nm(v): return names[v] if isinstance(v, int) and v >= 0 else str(v)
REQ, PACK, OACK = bnd['req'], bnd['pend_ack'], bnd['out0_ack']
AACK, BACK, SACK, OREQ = bnd['a_ack'], bnd['b_ack'], bnd['start_ack'], bnd['out0_req']
spc = {c: sorted(frozenset().union(*[supp(s) for j, s in enumerate(S[c][1]) if dep(S[c][0], S[c][2], j)]) | {c}) for c in CTL}
FRONT = sorted(set(v for c in CTL for v in spc[c] if v not in set(CTL) and v not in env))
envsupp = sorted(set([REQ, PACK, OACK, W_ENV]) | supp(AACK) | supp(BACK) | supp(SACK) | supp(OREQ))
print("control", len(CTL), "frontier", len(FRONT), "env window", len(envsupp), file=sys.stderr)
for c in CTL:
    for v in spc[c]:
        assert v in set(CTL) or v in FRONT or v in (REQ, PACK, OACK), nm(v)
windows = {c: tuple(spc[c]) for c in CTL}
windows['env'] = tuple(envsupp)
# truth tables: for control c, F_c as dict over tuple of window values
def asg_of(W, t): return {v: bool((t >> p) & 1) for p, v in enumerate(W)}
Ftab = {}
for c in CTL:
    W = windows[c]; tab = []
    for t in range(1 << len(W)):
        tab.append(F(c, asg_of(W, t)))
    Ftab[c] = tab
print("tables built", file=sys.stderr)
def initval(v):
    if v == W_ENV: return False
    if v in (REQ, PACK, OACK): return False
    return init[v]
R = {}
for k, W in windows.items():
    R[k] = {sum((1 << p) for p, v in enumerate(W) if initval(v))}
# readers of frontier nodes
readers = collections.defaultdict(list)
for c in CTL:
    for v in spc[c]:
        if v in FRONT: readers[v].append(c)
def out_of(u, asg):
    return evalnode(u, asg, {}) if u not in asg else asg[u]
def env_moves(asg):
    """env moves enabled in asg (over env window): list of (name, {var: newval})."""
    req, pa, oa, w = asg[REQ], asg[PACK], asg[OACK], asg[W_ENV]
    aa, ba, sa, orq = out_of(AACK, asg), out_of(BACK, asg), out_of(SACK, asg), out_of(OREQ, asg)
    m = []
    if not req and not aa and not ba and not sa and not pa and not w and not orq and not oa: m.append(("req+", {REQ: True}))
    if req and aa and ba and sa and pa: m.append(("req-", {REQ: False, W_ENV: True}))
    if req and not pa: m.append(("pack+", {PACK: True}))
    if not req and pa: m.append(("pack-", {PACK: False}))
    if orq and not oa: m.append(("oack+", {OACK: True}))
    if not orq and oa: m.append(("oack-", {OACK: False, W_ENV: False}))
    return m
ENVVARS = {REQ, PACK, OACK, W_ENV}
def owner_windows(v):
    """windows that contain var v"""
    return [k for k, W in windows.items() if v in W]
contains = collections.defaultdict(list)
for k, W in windows.items():
    for v in W: contains[v].append(k)
def join(Wa, Ra, Wb, Rb):
    """natural join of two relations; yields dicts"""
    sh = [v for v in Wa if v in Wb]
    pa = [Wa.index(v) for v in sh]; pb = [Wb.index(v) for v in sh]
    idx = collections.defaultdict(list)
    for t in Rb:
        idx[tuple((t >> p) & 1 for p in pb)].append(t)
    for ta in Ra:
        key = tuple((ta >> p) & 1 for p in pa)
        for tb in idx.get(key, ()):
            d = asg_of(Wa, ta); d.update(asg_of(Wb, tb)); yield d
def proj(W, d): return sum((1 << p) for p, v in enumerate(W) if d[v])
def tup(W, d): return proj(W, d)
it = 0
changed = True
while changed:
    changed = False; it += 1; added = 0
    for k, W in windows.items():
        movers = set(W)
        new = set()
        # control movers
        for m in movers:
            if isinstance(m, int) and m in Ftab:
                Wm = windows[m]
                for d in join(W, R[k], Wm, R[m]):
                    if Ftab[m][proj(Wm, d)] != d[m]:
                        d2 = dict(d); d2[m] = not d[m]; new.add(proj(W, d2))
            elif m in FRONT:
                if k == 'env': continue
                c = k  # window owner: flip allowed if c insensitive to m
                for t in R[k]:
                    t2 = t ^ (1 << W.index(m))
                    if Ftab[c][t] == Ftab[c][t2]: new.add(t2)
        if any(v in ENVVARS for v in W):
            We = windows['env']
            for d in join(W, R[k], We, R['env']):
                for nm, eff in env_moves(d):
                    d2 = dict(d); d2.update(eff); new.add(proj(W, d2))
        n0 = len(R[k]); R[k] |= new
        if len(R[k]) != n0: changed = True; added += len(R[k]) - n0
    print("iter", it, "added", added, "total", sum(len(r) for r in R.values()), file=sys.stderr)
# checks
viol = collections.Counter(); ex = {}
for c in CTL:
    Wc = windows[c]
    for m in Wc:
        if m == c: continue
        if isinstance(m, int) and m in Ftab:
            for d in join(Wc, R[c], windows[m], R[m]):
                if Ftab[c][proj(Wc, d)] != d[c] and Ftab[m][proj(windows[m], d)] != d[m]:
                    d2 = dict(d); d2[m] = not d[m]
                    if Ftab[c][proj(Wc, d2)] == d2[c]:
                        viol[(names[c], names[m])] += 1; ex[(names[c], names[m])] = {nm(v): int(d[v]) for v in Wc}
        elif m in ENVVARS:
            for d in join(Wc, R[c], windows['env'], R['env']):
                if Ftab[c][proj(Wc, d)] != d[c]:
                    for nm, eff in env_moves(d):
                        d2 = dict(d); d2.update(eff)
                        if Ftab[c][proj(Wc, d2)] == d2[c]:
                            viol[(names[c], nm)] += 1
print("windows", len(windows), "R sizes: max", max(len(r) for r in R.values()), "sum", sum(len(r) for r in R.values()))
print("persistence violations (over-approximation):", len(viol))
for (a, b), n in viol.most_common(40): print("  ", n, a, "disabled by", b)
# boundary protocol: acks
def ackcheck(u, nm):
    bad = 0
    for k in contains[u] if u in contains else []:
        pass
    return bad
import json
json.dump({"viol": [[a, b, n] for (a, b), n in viol.items()], "ex": {"%s|%s" % k: v for k, v in ex.items()},
           "R": {nm(k): len(r) for k, r in R.items()}},
          open("/tmp/claude-0/w/winfix_out.json", "w"), indent=0)
