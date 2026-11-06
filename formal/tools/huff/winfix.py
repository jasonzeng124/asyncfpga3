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
import pickle, os
TCACHE = sys.argv[1] + ".ftab.pkl"
if os.path.exists(TCACHE): Ftab = pickle.load(open(TCACHE, "rb"))
for c in CTL:
    if c in Ftab: continue
    W = windows[c]; tab = []
    for t in range(1 << len(W)):
        tab.append(F(c, asg_of(W, t)))
    Ftab[c] = tab
pickle.dump(Ftab, open(TCACHE, "wb"))
print("tables built", file=sys.stderr)
if "--export" in sys.argv:
    with open(sys.argv[sys.argv.index("--export") + 1], "w") as f:
        f.write("%d\n" % len(windows))
        for k, W in windows.items():
            f.write("%s %d %s\n" % ("env" if k == "env" else str(k), len(W), " ".join(str(v) for v in W)))
    print("exported windows", file=sys.stderr); sys.exit(0)
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

# ---- fast fixpoint (bit operations; same semantics as the join version) ----
pos = {k: {v: p for p, v in enumerate(W)} for k, W in windows.items()}
def keyfun(A, B):
    """positions in A and in B of the variables they share"""
    sh = [v for v in windows[A] if v in pos[B]]
    return [pos[A][v] for v in sh], [pos[B][v] for v in sh]
def key(t, ps):
    r = 0
    for i, p in enumerate(ps):
        if (t >> p) & 1: r |= 1 << i
    return r
KF = {}
def kf(A, B):
    if (A, B) not in KF: KF[(A, B)] = keyfun(A, B)
    return KF[(A, B)]
ENVMOVES = ["req+", "req-", "pack+", "pack-", "oack+", "oack-"]
def env_enabled_effects(t):
    d = asg_of(windows['env'], t)
    return env_moves(d)
movers = {}
for k, W in windows.items():
    ms = []
    for v in W:
        if isinstance(v, int) and v in Ftab: ms.append(("ctl", v))
        elif v in FRONT and k != 'env': ms.append(("fr", v))
    if any(v in ENVVARS for v in W): ms.append(("env", None))
    movers[k] = ms
def excited_keys(m, A):
    pa, pb = kf(A, m)
    Wm = windows[m]; pm = pos[m][m]
    return set(key(t, pb) for t in R[m] if Ftab[m][t] != bool((t >> pm) & 1))
def env_keys(A):
    """for each env move: set of keys (on A ∩ env window) where enabled; effects"""
    pa, pb = kf(A, 'env')
    out = collections.defaultdict(set); effs = {}
    for t in R['env']:
        for nm_, eff in env_enabled_effects(t):
            out[nm_].add(key(t, pb)); effs[nm_] = eff
    return pa, out, effs

RCACHE = sys.argv[1] + ".R.pkl"
if os.path.exists(RCACHE) and "--fresh" not in sys.argv: R = pickle.load(open(RCACHE, "rb"))
if "--seed-obs" in sys.argv:
    # candidate invariant: the tuples observed in concrete runs (huffx --walks); then close it
    for ln in open(sys.argv[sys.argv.index("--seed-obs") + 1]):
        k, *ts = ln.split(); k = "env" if k == "env" else int(k)
        R[k] |= set(int(t) for t in ts)
    R0 = {k: set(r) for k, r in R.items()}

if "--ctx" in sys.argv:
    # context-consistent closure: a joined pair (t on W, tm on W_m) is kept only if, for every other
    # window X sharing >= 2 variables with W ∪ W_m, some allowed tuple of X agrees with it there.
    # Sound (the real state meets every window); Lean: WinInv closeCtxOK (to be written).
    allv = {}
    def ctxw(k, m):
        ck = (k, m)
        if ck in allv: return allv[ck]
        U = set(windows[k]) | set(windows[m])
        xs = []
        for X, WX in windows.items():
            if X in (k, m): continue
            I = [v for v in WX if v in U]
            if len(I) >= 2: xs.append((X, I))
        allv[ck] = xs; return xs
    projc = {}
    def projset(X, I):
        ck = (X, tuple(I))
        if ck in projc and projc[ck][0] == len(R[X]): return projc[ck][1]
        ps = [pos[X][v] for v in I]
        r = set(key(t, ps) for t in R[X]); projc[ck] = (len(R[X]), r); return r
    def consistent(d, xs):
        for X, I in xs:
            kk = 0
            for i, v in enumerate(I):
                if d[v]: kk |= 1 << i
            if kk not in projset(X, I): return False
        return True
    def asg2(Wa, ta, Wb, tb):
        d = {}
        for p_, v in enumerate(Wa): d[v] = bool((ta >> p_) & 1)
        for p_, v in enumerate(Wb):
            bv = bool((tb >> p_) & 1)
            if v in d and d[v] != bv: return None
            d[v] = bv
        return d
    sweep = 0; changed = True
    while changed:
        changed = False; sweep += 1; added = 0
        for k, W in windows.items():
            new = set()
            for kind, m in movers[k]:
                if kind == "ctl" or kind == "env":
                    mk = m if kind == "ctl" else 'env'
                    Wm = windows[mk]; xs = ctxw(k, mk)
                    if mk == k:
                        for t in R[k]:
                            if kind == "ctl" and Ftab[m][t] != bool((t >> pos[k][m]) & 1): new.add(t ^ (1 << pos[k][m]))
                        continue
                    for tm in R[mk]:
                        if kind == "ctl":
                            if Ftab[m][tm] == bool((tm >> pos[mk][m]) & 1): continue
                            effl = [({m: not bool((tm >> pos[mk][m]) & 1)})]
                        else:
                            effl = [e for _, e in env_enabled_effects(tm)]
                            if not effl: continue
                        for t in R[k]:
                            d = asg2(W, t, Wm, tm)
                            if d is None or not consistent(d, xs): continue
                            for eff in effl:
                                t2 = t
                                for v, bb in eff.items():
                                    if v in pos[k]:
                                        p_ = pos[k][v]; t2 = (t2 | (1 << p_)) if bb else (t2 & ~(1 << p_))
                                new.add(t2)
                elif kind == "fr":
                    b_ = 1 << pos[k][m]
                    for t in R[k]:
                        if Ftab[k][t] == Ftab[k][t ^ b_]: new.add(t ^ b_)
            n0 = len(R[k]); R[k] |= new
            if len(R[k]) != n0: changed = True; added += len(R[k]) - n0
        print("ctx sweep", sweep, "added", added, "total", sum(len(r) for r in R.values()), file=sys.stderr)
    work = []
else:
    work = None
# chaotic iteration with a worklist: a window is revisited only when its own relation or the
# relation of one of its movers' windows grew (same least fixpoint as the sweep)
deps = collections.defaultdict(set)   # deps[j] = windows whose update reads R[j]
for k in windows:
    deps[k].add(k)
    for kind, m in movers[k]:
        if kind == "ctl": deps[m].add(k)
        elif kind == "env": deps['env'].add(k)
ver = {k: 0 for k in windows}; cacheEK = {}
def excited_keys_c(m, A):
    ck = (m, A)
    if ck in cacheEK and cacheEK[ck][0] == ver[m]: return cacheEK[ck][1]
    r = excited_keys(m, A); cacheEK[ck] = (ver[m], r); return r
cacheEnv = {}
def env_keys_c(A):
    if A in cacheEnv and cacheEnv[A][0] == ver['env']: return cacheEnv[A][1]
    r = env_keys(A); cacheEnv[A] = (ver['env'], r); return r
if work is None:
    work = collections.deque(windows.keys())
else:
    work = collections.deque()
inwork = set(work); steps = 0
while work:
    k = work.popleft(); inwork.discard(k); steps += 1
    new = set()
    for kind, m in movers[k]:
        if kind == "ctl":
            pa, _ = kf(k, m); EK = excited_keys_c(m, k); b = 1 << pos[k][m]
            for t in R[k]:
                if key(t, pa) in EK: new.add(t ^ b)
        elif kind == "fr":
            b = 1 << pos[k][m]
            for t in R[k]:
                if Ftab[k][t] == Ftab[k][t ^ b]: new.add(t ^ b)
        else:
            pa, EKs, effs = env_keys_c(k)
            for nm_, ks in EKs.items():
                eff = effs[nm_]
                for t in R[k]:
                    if key(t, pa) in ks:
                        t2 = t
                        for v, bb in eff.items():
                            if v in pos[k]:
                                p = pos[k][v]; t2 = (t2 | (1 << p)) if bb else (t2 & ~(1 << p))
                        new.add(t2)
    n0 = len(R[k]); R[k] |= new
    if len(R[k]) != n0:
        ver[k] += 1
        for j in deps[k]:
            if j not in inwork: work.append(j); inwork.add(j)
    if steps % 20000 == 0: print("steps", steps, "work", len(work), "total", sum(len(r) for r in R.values()), file=sys.stderr)
if "--seed-obs" in sys.argv:
    grown = {k: len(R[k]) - len(R0[k]) for k in R if len(R[k]) != len(R0[k])}
    print("closure added tuples to", len(grown), "windows; total added", sum(grown.values()), file=sys.stderr)
    for k, n in sorted(grown.items(), key=lambda t: -t[1])[:15]: print("   grew", nm(k), n, "observed", len(R0[k]), file=sys.stderr)
else: pickle.dump(R, open(RCACHE, "wb"))
print("fixpoint after", steps, "window visits; total tuples", sum(len(r) for r in R.values()), file=sys.stderr)
# checks: persistence of every excited control node under every other move that can touch its window
viol = collections.Counter(); ex = {}
for c in CTL:
    Wc = windows[c]; pc = pos[c][c]
    exc = [t for t in R[c] if Ftab[c][t] != bool((t >> pc) & 1)]
    for kind, m in movers[c]:
        if kind == "ctl" and m != c:
            pa, pb = kf(c, m); EK = excited_keys(m, c); b = 1 << pos[c][m]
            for t in exc:
                if key(t, pa) in EK and Ftab[c][t ^ b] == bool((t >> pc) & 1):
                    viol[(nm(c), nm(m))] += 1; ex[(nm(c), nm(m))] = t
        elif kind == "env":
            pa, EKs, effs = env_keys(c)
            for mvn, ks in EKs.items():
                for t in exc:
                    if key(t, pa) in ks:
                        t2 = t
                        for v, bb in effs[mvn].items():
                            if v in pos[c]:
                                p = pos[c][v]; t2 = (t2 | (1 << p)) if bb else (t2 & ~(1 << p))
                        if Ftab[c][t2] == bool((t2 >> pc) & 1): viol[(nm(c), mvn)] += 1
print("windows", len(windows), "R sizes: max", max(len(r) for r in R.values()), "sum", sum(len(r) for r in R.values()))
big = sorted(((len(r), nm(k)) for k, r in R.items()), reverse=True)[:8]
print("largest windows", big)
print("persistence violations (over-approximation):", len(viol), "pairs")
for (x, y), n in viol.most_common(60): print("  ", n, x, "disabled by", y)
# bundling obligations: per frontier node, how many reachable reader tuples are sensitive to it
bo = collections.Counter()
for c in CTL:
    for v in windows[c]:
        if v in FRONT:
            b = 1 << pos[c][v]
            bo[nm(v)] += sum(1 for t in R[c] if Ftab[c][t] != Ftab[c][t ^ b])
print("BO_f: frontier nodes with sensitive reader tuples:", sum(1 for k in bo if bo[k]), "of", len(FRONT))
import json
json.dump({"viol": [[x, y, n] for (x, y), n in viol.items()], "bo": dict(bo),
           "R": {nm(k): len(r) for k, r in R.items()}}, open(sys.argv[1] + ".winfix.json", "w"), indent=0)
