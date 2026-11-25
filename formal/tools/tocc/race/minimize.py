#!/usr/bin/env python3
"""Shard C (UNTRUSTED): TO rows split + L weakening for one corner.
(1) Split TO rows: T1 = a is the reader v itself and (b, m-1) was already read when one of v's events (v, j<=k)
    fired (it, or a later b event, is a direct cause of such an event): physically implied by monotone reads +
    ChangeOK, but TimedOcc.TO as stated still demands it.  T2 = all other rows (reconvergent reads).
(2) Weaken L: for every (a,k,b) with a failing T2 row, lower L(a,k,b) to the largest m' whose row passes for every
    reader (any smaller L stays LSound/LStep-valid); re-run LCheck with the weakened L, then the reader-level timed
    exclusion (Sep - Up, outside the Lean theorems) on the new failures.
usage: minimize.py c"""
import sys, time, pickle, collections
sys.path.insert(0, "/tmp/claude-0/race")
import cert
from cert import build
from lcheck import check_node
from timing import Tm, INF
c = int(sys.argv[1]); T0 = time.time()
K = build(c, "all"); C = K["C"]; nm = C["names"]; ev = K["ev"]; eid = K["eid"]; tm = Tm(K)
A = pickle.load(open("/tmp/claude-0/race/an_c%d_all.pkl" % c, "rb")); rows = A["rows"]; res = A["res"]
def lo_(v, w): return 1 if v in K["envnode"] else (K["dl"][(v, w)][0] if (v, w) in K["dl"] else 1)
def hi_(v, w): return 1 if v in K["envnode"] else (K["dl"][(v, w)][1] if (v, w) in K["dl"] else 1)
def mono_cov(v, k, b, mb):
    for j in range(k + 1):
        for (w, i) in K["causes"][(v, j)]:
            if w == b and i >= mb: return True
    return False
T1 = []; T1x = []; T2 = []
for r in rows:
    m, v, a, k, b, mb, s, need = r
    if a == v and mono_cov(v, k, b, mb): T1.append(r)
    elif a == v: T1x.append(r)
    else: T2.append(r)
f = lambda L_: sum(1 for r in L_ if r[0] < 0)
print("[c=%d] TO rows %d: T1 (a = reader, implied by monotone reads) %d (failed as stated %d); a = reader but not implied %d (failed %d); T2 %d (failed %d)" % (
    c, len(rows), len(T1), f(T1), len(T1x), f(T1x), len(T2), f(T2)))
print("  worst T2 rows:")
for r in sorted(T2)[:10]:
    m, v, a, k, b, mb, s, need = r
    print("   margin %5d  v=%s  a=%s(%d) b=%s(%d)  Sep=%d  hi(v,b)-lo(v,a)=%d" % (m, nm[v], nm[a], k, nm[b], mb, s, need))
print("  worst a=reader-not-implied rows:")
for r in sorted(T1x)[:5]:
    m, v, a, k, b, mb, s, need = r
    print("   margin %5d  v=%s  a=%s(%d) b=%s(%d)  Sep=%d  need=%d" % (m, nm[v], nm[a], k, nm[b], mb, s, need))
# ---- weaken L
needmax = collections.defaultdict(int)
for r in T2 + T1x:
    m, v, a, k, b, mb, s, need = r
    needmax[(a, k, b)] = max(needmax[(a, k, b)], need)
over = {}
for r in T2 + T1x:
    if r[0] >= 0: continue
    m, v, a, k, b, mb, s, need = r
    key = (a, k, b)
    if key in over: continue
    mm = mb + 1
    while mm > 0:
        sp = tm.sep(eid[(b, mm - 1)], eid[(a, k)])
        if sp is not None and sp >= needmax[key]: break
        mm -= 1
    over[key] = mm
print("  weakened L entries: %d (to 0: %d)" % (len(over), sum(1 for x in over.values() if x == 0)))
oldL = cert.L
def Lw(K_, a, k, b):
    x = oldL(K_, a, k, b)
    return min(x, over.get((a, k, b), x))
cert.L = Lw
import lcheck; lcheck.L = Lw
nvec = 0; fails = []
for v in sorted(C["EXACT"]):
    r = check_node(K, v, cap=10**6); nvec += r["nvec"]
    fails += [(v, kind, n, r["D"]) for kind, n in r["ex"]]
print("  LCheck with weakened L: vectors %d, failures %d %s, failing nodes %d (%.0fs)" % (
    nvec, len(fails), dict(collections.Counter(x[1] for x in fails)), len(set(x[0] for x in fails)), time.time() - T0))
cache = {}; excl = []; kept = []
for (v, kind, n, D) in fails:
    if kind == "X": kept.append((v, kind, n, None)); continue
    best = None
    for iu, u in enumerate(D):
        if n[iu] >= len(ev[u]): continue
        U = eid[(u, n[iu])]
        for iw, w in enumerate(D):
            if iw == iu or n[iw] == 0: continue
            W = eid[(w, n[iw] - 1)]
            if tm.leq(U, W): continue
            if (U, W) not in cache: cache[(U, W)] = tm.best_order(U, W)
            bnd, e0 = cache[(U, W)]
            if bnd == -INF: continue
            mg = bnd - (hi_(v, u) - lo_(v, w))
            if best is None or mg > best[0]: best = (mg, u, n[iu], w, n[iw] - 1, e0, bnd)
    (excl if best is not None and best[0] >= 0 else kept).append((v, kind, n, best))
print("  timed exclusion (Sep - Up, reader-level): %d excluded, %d remain %s (%.0fs)" % (
    len(excl), len(kept), dict(collections.Counter(x[1] for x in kept)), time.time() - T0))
# RT-style edges: distinct (U before W) orders used, event-level margin Sep(e0->W) - Up(e0->U) - 1 and reader margin
edges = {}
for (v, kind, n, best) in excl:
    mg, u, iu, w, iw, e0, bnd = best
    key = ((u, iu), (w, iw))
    if key not in edges or mg < edges[key][0]: edges[key] = (mg, bnd - 1, v, e0)
evm = [x[1] for x in edges.values()]
print("  distinct order edges used: %d; reader-level margin min %d; event-level (Sep-Up-1) min %d, #negative %d" % (
    len(edges), min(x[0] for x in edges.values()) if edges else 0, min(evm) if evm else 0, sum(1 for x in evm if x < 0)))
for key, (mg, em, v, e0) in sorted(edges.items(), key=lambda x: x[1][0])[:8]:
    (u, iu), (w, iw) = key
    print("   %s(%d) before %s(%d) at reader %s: reader margin %d, event margin %d, e0=%s(%d)" % (
        nm[u], iu, nm[w], iw, nm[v], mg, em, nm[K["elist"][e0][0]], K["elist"][e0][1]))
print("  worst remaining (not excluded):")
for (v, kind, n, best) in sorted(kept, key=lambda x: (x[3][0] if x[3] else -INF))[:10]:
    print("   %s %s %s n=%s best=%s" % (nm[v], "CTRL" if v in C["CTRL"] else "", kind, n,
          best and (best[0], nm[best[1]], best[2], nm[best[3]], best[4])))
pickle.dump(dict(over=over, fails=fails, excl=excl, kept=kept, edges=edges, T1=T1, T1x=T1x, T2=T2),
            open("/tmp/claude-0/race/min_c%d.pkl" % c, "wb"))
