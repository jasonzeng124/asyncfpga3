#!/usr/bin/env python3
"""Shard C (UNTRUSTED): timed margin of a relative-timing order "c fires before b" from an abstract trace
(huffx --trace). In the trace, b's move disables c's excitation. Causes: each fired storage node's cause is
the support node (storage or env, through zero-delay logic) that changed last before it fired. From the
two backward cause chains (of b's move, and of the event e that excited c) take their first common event A.
Race: c must switch, through its routed loop, before b fires:
   D = max delay  A -> ... -> e -> c's pin, plus c's own loop (its clean-switch time, SpecLoop.cgate_switch)
   L = min delay  A -> ... -> b
using, per hop u -> v, the extreme sums of the netlist's per-arc prjxray numbers over every logic path from
u's output to a pin of v (copy chains included). At corner c in {0, 1} (fast, slow; g = 1): the order holds
for scatter kappa < kappa* = (L - D) / (L + D), a SUFFICIENT bound (paths may be unsensitised).
usage: rtmargin.py net.json bnd.json TRACE... (file names C__B__k.txt from huffx --traceall)"""
import json, sys, collections, heapq
net = json.load(open(sys.argv[1])); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
BJ = json.load(open(sys.argv[2])); B = BJ["boundary"]; ENV = set(idx[x] for x in BJ["env"])
def is_copy(g): return g["k"] == 1 and g["init"] == 2
def dep(g, j):
    k, I = g["k"], g["init"]
    return any(((I >> x) & 1) != ((I >> (x ^ (1 << j))) & 1) for x in range(1 << k))
cm = {i: g for i, g in enumerate(G) if is_copy(g) and i not in ENV}
def chain(u):
    """source and summed arcs (fmin, fmax, smin, smax) of the copy chain ending at node u"""
    s = [0, 0, 0, 0]
    while u in cm:
        a = cm[u]["arcs"][0]; s = [s[0] + a["fmin"], s[1] + a["fmax"], s[2] + a["smin"], s[3] + a["smax"]]
        u = cm[u]["ins"][0]
    return u, s
logic = [i for i, g in enumerate(G) if not is_copy(g) and i not in ENV]
pins = {}
for i in logic:
    ps = []
    for j, u in enumerate(G[i]["ins"]):
        if not dep(G[i], j): continue
        s, d = chain(u); a = G[i]["arcs"][j]
        ps.append((s, (d[0] + a["fmin"], d[1] + a["fmax"], d[2] + a["smin"], d[3] + a["smax"])))
    pins[i] = ps
stor = {i for i in logic if any(s == i for s, _ in pins[i])}
succ = collections.defaultdict(list)
for i in logic:
    for s, d in pins[i]: succ[s].append((i, d))
def hop(u, v, f, mode):
    """extreme sum of arc field f over logic paths u -> (comb)* -> pin of v; mode min or max; None if no path"""
    best = {}; out = None
    # DAG through comb nodes: relax in a priority order (Dijkstra for min, longest path by DFS memo for max)
    if mode == "min":
        h = [(0, u)]; dist = {u: 0}
        while h:
            d0, x = heapq.heappop(h)
            if d0 > dist.get(x, 1e18): continue
            for y, d in succ[x]:
                nd = d0 + d[f]
                if y == v:
                    out = nd if out is None else min(out, nd); continue
                if y in stor or y in ENV: continue
                if nd < dist.get(y, 1e18): dist[y] = nd; heapq.heappush(h, (nd, y))
        return out
    memo = {}
    def lp(x):   # longest from x to a pin of v (x is u or comb)
        if x in memo: return memo[x]
        r = None
        for y, d in succ[x]:
            if y == v: c = d[f]
            elif y in stor or y in ENV: continue
            else:
                t = lp(y); c = None if t is None else d[f] + t
            if c is not None: r = c if r is None else max(r, c)
        memo[x] = r; return r
    return lp(u)
# storage-level supports
memo2 = {}
sup = {}
sys.setrecursionlimit(100000)
def ssupp(v):
    """storage/env nodes whose change can reach v through logic"""
    res = set(); st = [v]; seen = set()
    for s, _ in pins[v]:
        st.append(s)
    st = [s for s, _ in pins[v]]
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x)
        if x in stor or x in ENV or x not in pins: res.add(x); continue
        for s, _ in pins[x]: st.append(s)
    return res
envmap = {"env-1": idx[B["req"]], "env-2": idx[B["req"]], "env-3": idx[B["pend_ack"]], "env-4": idx[B["pend_ack"]],
          "env-5": idx[B["out0_ack"]], "env-6": idx[B["out0_ack"]]}
results = []
import os
def one(path, CN):
    trace = [l.strip() for l in open(path) if l.strip() and not l.startswith("#")]
    ev = [envmap[t] if t.startswith("env") else idx[t] for t in trace]
    last = {}; cause = [None] * len(ev)
    for t, v in enumerate(ev):
        if v in pins:
            if v not in sup: sup[v] = ssupp(v)
            cands = [(last[u], u) for u in sup[v] if u != v and u in last]
            cause[t] = max(cands)[0] if cands else None
        last[v] = t
    def back(t):
        ch = []
        while t is not None: ch.append(t); t = cause[t]
        return ch
    tb = len(ev) - 1; b = ev[tb]
    # event that excited c: last change of a support of c before b's move
    if CN not in sup: sup[CN] = ssupp(CN)
    te = max(t for t in range(tb) if ev[t] in sup[CN] and ev[t] != CN)
    cb, ce = back(tb), back(te)
    common = set(cb) & set(ce); A = max(common) if common else None
    def chain_delay(ch, A, f, mode):
        """sum of hop delays along a cause chain from A forward"""
        seq = list(reversed(ch[:ch.index(A) + 1]))  # A ... last
        tot = 0
        for x, y in zip(seq, seq[1:]):
            d = hop(ev[x], ev[y], f, mode)
            if d is None: return None
            tot += d
        return tot, len(seq) - 1
    name = lambda v: N[v]
    print("race: c =", N[CN], " b =", name(b), " e (excites c) =", name(ev[te]), "at", te, " common cause A =", name(ev[A]) if A is not None else None, "at", A)
    for corner, (fl, fu) in enumerate([(0, 1), (2, 3)]):
        Lr = chain_delay(cb, A, fl, "min"); Dr = chain_delay(ce, A, fu, "max")
        if Lr is None or Dr is None: print("corner", corner, "no path", Lr, Dr); continue
        L, nl = Lr; D0, nd = Dr
        toc = hop(ev[te], CN, fu, "max"); loop = hop(CN, CN, fu, "max")
        D = D0 + toc + loop
        print("corner %d: L (A->b, %d hops, min) = %d ps; D (A->e %d hops + e->c %d + c loop %d, max) = %d ps; kappa* = %.3f" % (
            corner, nl, L, nd, toc, loop, D, (L - D) / (L + D)))

for path in sys.argv[3:]:
    CN = idx[os.path.basename(path).split("__")[0]]
    print("==", os.path.basename(path)); one(path, CN)
if os.environ.get("DETAIL"):
    path = sys.argv[3]; CN = idx[os.path.basename(path).split("__")[0]]
    trace = [l.strip() for l in open(path) if l.strip() and not l.startswith("#")]
    ev = [envmap[t] if t.startswith("env") else idx[t] for t in trace]
    last = {}; cause = [None] * len(ev)
    for t, v in enumerate(ev):
        if v in pins:
            if v not in sup: sup[v] = ssupp(v)
            cands = [(last[u], u) for u in sup[v] if u != v and u in last]
            cause[t] = max(cands)[0] if cands else None
        last[v] = t
    def back(t):
        ch = []
        while t is not None: ch.append(t); t = cause[t]
        return ch
    tb = len(ev) - 1
    if CN not in sup: sup[CN] = ssupp(CN)
    te = max(t for t in range(tb) if ev[t] in sup[CN] and ev[t] != CN)
    cb, ce = back(tb), back(te); A = max(set(cb) & set(ce))
    bel = json.load(open("/tmp/claude-0/w/bel2cell.json"))
    nmf = lambda v: bel.get(N[v], N[v]).replace("bridge_i.udut.", "")
    for lab, ch, f, mode in (("b-chain (min fast)", cb, 0, "min"), ("e-chain (max fast)", ce, 1, "max")):
        seq = list(reversed(ch[:ch.index(A) + 1])); print(lab)
        for x, y in zip(seq, seq[1:]): print("   %6d -> %6d  %-55s -> %-55s %s" % (x, y, nmf(ev[x])[:55], nmf(ev[y])[:55], hop(ev[x], ev[y], f, mode)))
    print("e->c max fast", hop(ev[te], CN, 1, "max"), nmf(ev[te]), "->", nmf(CN))
