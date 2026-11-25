#!/usr/bin/env python3
"""Shard B (UNTRUSTED): which storage gates of a decoded netlist are C-elements in the sense of
Formal.Cells.SpecCElem (INIT facts hall/hhold for some input polarity, constant pins = sources that are
constant gates or the reset node held low), and the margin of SpecCElem.celem_forced on each, with
Δ_i = the shortest path from q's output to input i's SOURCE node (all-paths, support pins; a sufficient value
for the timing half of hA when input i's change is a response to q's change): hloop: hi_j <= Δ_i + lo_i for
every C input; separation: max_i (Δ_i + lo_i) >= every C input's hi_i (M = max hi_i, i0 = the argmax). Per
corner c in {0,1} (FAST/SLOW numbers), κ-scaled: hi = (1+κ)·Σmax, lo = (1-κ)·Σmin, dist = (1-κ)·Σmin.
Reports the largest κ (grid 0.005, g = 1) at which both hold, per gate (inputs with no return path within the
search limit count as satisfied, which needs Δ_i >= 4·max(hi) -- reported as kstar >= 0.6 if all are such).
usage: celemtab.py NET.json ARBS.json RESETNODE OUT.json"""
import json, sys, heapq, itertools
N = json.load(open(sys.argv[1])); g = N["gates"]; arbq = {a["qi"] for a in json.load(open(sys.argv[2]))}
RST = int(sys.argv[3]); nn = len(N["nodes"])
drv = {G["out"]: i for i, G in enumerate(g)}
def dep(G, p):
    k, I = G["k"], G["init"]
    return any(((I >> a) & 1) != ((I >> (a | (1 << p))) & 1) for a in range(1 << k) if not a >> p & 1)
fan = [[] for _ in range(nn)]
for gi, G in enumerate(g):
    for p, m in enumerate(G["ins"]):
        if dep(G, p): fan[m].append((gi, p))
def chain(n, stop=None):
    m, ch = n, []
    while m in drv and g[drv[m]]["k"] == 1 and g[drv[m]]["init"] == 2 and m != stop and len(ch) < 80:
        ch.append(drv[m]); m = g[drv[m]]["ins"][0]
    return m, ch
def isconst(m): return m in drv and g[drv[m]]["k"] == 0
def cval(m): return g[drv[m]]["init"] & 1
def classify(gi):
    G = g[gi]; k = G["k"]; fb = None; srcs = []
    for j, n in enumerate(G["ins"]):
        m, ch = chain(n, G["out"]); srcs.append((m, ch))
        if m == G["out"] and fb is None: fb = j
    if fb is None: return None
    ov = {}; ci = []
    for i, (m, ch) in enumerate(srcs):
        if i == fb: continue
        if isconst(m): ov[i] = cval(m)
        elif not dep(G, i): ov[i] = 0
        elif m == RST: ov[i] = 0
        else: ci.append(i)
    if not ci: return None
    out = lambda v: (G["init"] >> sum(b << i for i, b in enumerate(v))) & 1
    for pol in itertools.product([0, 1], repeat=len(ci)):
        P = dict(zip(ci, pol)); ok = True
        for bits in itertools.product([0, 1], repeat=len(ci) + 1):
            v = [0] * k
            for i, b in ov.items(): v[i] = b
            for i, b in zip(ci, bits): v[i] = b
            v[fb] = bits[-1]; e = [v[i] ^ P[i] for i in ci]; o = out(v)
            if all(x == e[0] for x in e) and o != e[0]: ok = False; break
            if not all(x == e[0] for x in e) and o != v[fb]: ok = False; break
        if ok: return fb, ci, P, ov, srcs
    return None
def comp(gi, i, srcs, key):  # composite arcs of pin i: own arc + chain arcs
    return g[gi]["arcs"][i][key] + sum(g[c]["arcs"][0][key] for c in srcs[i][1])
def dist(src, targets, key, limit):
    d0 = {src: 0}; pq = [(0, src)]; res = {}
    while pq:
        d, m = heapq.heappop(pq)
        if d > d0[m] or d > limit: continue
        if m in targets and m not in res: res[m] = d
        for gi, p in fan[m]:
            o = g[gi]["out"]; nd = d + g[gi]["arcs"][p][key]
            if nd < d0.get(o, 1 << 60) and nd <= limit: d0[o] = nd; heapq.heappush(pq, (nd, o))
    return res
rows = []; nst = 0; nce = 0
for gi, G in enumerate(g):
    if G["k"] < 2: continue
    r = classify(gi)
    m0, _ = (None, None)
    if r is None:
        if any(chain(n, G["out"])[0] == G["out"] for n in G["ins"]): nst += 1
        continue
    nst += 1; nce += 1
    fb, ci, P, ov, srcs = r
    targets = {srcs[i][0] for i in ci}; pre = []
    for kmin, kmax in [("fmin", "fmax"), ("smin", "smax")]:
        L = comp(gi, fb, srcs, kmax); His = [comp(gi, i, srcs, kmax) for i in ci]
        H0 = max([L] + His); D = dist(G["out"], targets, kmin, 4 * H0 + 10)
        pre.append((L, His, [(D.get(srcs[i][0], 10 * H0), comp(gi, i, srcs, kmin)) for i in ci]))
    def ok(kk):
        for L, His, lst in pre:
            resp = [(1 - kk) * (Di + lo) for Di, lo in lst]
            if any(r < (1 + kk) * L for r in resp): return False
            if max(resp) < (1 + kk) * max(His): return False
        return True
    best = None
    for kk in [s * 0.005 for s in range(0, 121)]:
        if ok(kk): best = kk
        else: break
    rows.append(dict(q=gi, name=G["name"], arb=gi in arbq, fb=fb, ci=ci, pol=[P[i] for i in ci], kstar=best,
                     k=G["k"], ov=ov, chains=[[c for c in srcs[i][1]] for i in range(G["k"])],
                     srcs=[srcs[i][0] for i in range(G["k"])]))
rows.sort(key=lambda r: (r["kstar"] if r["kstar"] is not None else -1))
json.dump(rows, open(sys.argv[4], "w"))
print("storage gates", nst, "C-elements (SpecCElem sense)", nce)
for r in rows[:25]: print(r)
