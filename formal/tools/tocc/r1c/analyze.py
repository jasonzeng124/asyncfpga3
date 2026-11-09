#!/usr/bin/env python3
"""Shard C (UNTRUSTED): one corner, one cause mode: LCheck failures, their timed exclusion (reader-level order
U before W justified by Sep(e0->W) - Up(e0->U) >= hi'(v,u) - lo'(v,w)), and the TO rows (TimedOcc.TO).
usage: analyze.py c [mode]  -> an_c<c>_<mode>.pkl + printed summary"""
import sys, time, pickle, collections
sys.path.insert(0, "/tmp/claude-0/r1c")
from cert import build, L
from lcheck import check_node
from timing import Tm, INF
c = int(sys.argv[1]); mode = sys.argv[2] if len(sys.argv) > 2 else "all"
T0 = time.time()
K = build(c, mode); C = K["C"]; nm = C["names"]; ev = K["ev"]; tm = Tm(K); eid = K["eid"]
def lo_(v, w):
    if v in K["envnode"]: return 1
    return K["dl"][(v, w)][0] if (v, w) in K["dl"] else 1
def hi_(v, w):
    if v in K["envnode"]: return 1
    return K["dl"][(v, w)][1] if (v, w) in K["dl"] else 1
# ---------------- LCheck
res = {}
for v in sorted(C["EXACT"]):
    res[v] = check_node(K, v, cap=10**6)
nvec = sum(r["nvec"] for r in res.values()); maxD = max(len(r["D"]) for r in res.values())
fails = [(v, kind, n) for v, r in res.items() for (kind, n) in r["ex"]]
print("[c=%d %s] exact nodes %d, events %d, vectors %d, max|D| %d, failures %d %s, failing nodes %d (%.0fs)" % (
    c, mode, len(res), len(K["elist"]), nvec, maxD, len(fails), dict(collections.Counter(k for _, k, _ in fails)),
    sum(1 for r in res.values() if r["fails"]), time.time() - T0))
# ---------------- timed exclusion of the failing vectors
cache = {}
def order_bound(U, W):
    key = (U, W)
    if key not in cache: cache[key] = tm.best_order(U, W)
    return cache[key]
excl = []; kept = []
for (v, kind, n) in fails:
    if kind == "X": kept.append((v, kind, n, None)); continue
    D = res[v]["D"]; best = None
    for iu, u in enumerate(D):
        if n[iu] >= len(ev[u]): continue
        U = eid[(u, n[iu])]
        for iw, w in enumerate(D):
            if iw == iu or n[iw] == 0: continue
            W = eid[(w, n[iw] - 1)]
            if tm.leq(U, W): continue      # already excluded by L (should not happen)
            b, e0 = order_bound(U, W)
            if b == -INF: continue
            marg = b - (hi_(v, u) - lo_(v, w))
            if best is None or marg > best[0]: best = (marg, u, n[iu], w, n[iw] - 1, e0)
    if best is not None and best[0] >= 0: excl.append((v, kind, n, best))
    else: kept.append((v, kind, n, best))
print("  timed exclusion: %d of %d non-X failures excluded (margin >= 0); remaining %s (%.0fs)" % (
    len(excl), sum(1 for f in fails if f[1] != "X"), dict(collections.Counter(k for _, k, _, _ in kept)), time.time() - T0))
# ---------------- TO rows
rows = []
for v in sorted(C["EXACT"]):
    if v in K["envnode"]: continue
    D = res[v]["D"]
    for a in D:
        for b in D:
            if a == b: continue
            for k in range(len(ev[a])):
                m = L(K, a, k, b)
                if m == 0: continue
                need = hi_(v, b) - lo_(v, a)
                if need <= 0: continue
                s = tm.sep(eid[(b, m - 1)], eid[(a, k)])
                rows.append((s - need, v, a, k, b, m - 1, s, need))
fail_to = [r for r in rows if r[0] < 0]
print("  TO rows %d, failed %d (%.0fs)" % (len(rows), len(fail_to), time.time() - T0))
pickle.dump(dict(res={v: dict(D=r["D"], nvec=r["nvec"], fails=dict(r["fails"])) for v, r in res.items()},
                 fails=fails, excl=excl, kept=kept, rows=rows), open("/tmp/claude-0/r1c/an_c%d_%s.pkl" % (c, mode), "wb"))
