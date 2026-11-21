#!/usr/bin/env python3
"""Shard C (UNTRUSTED): data layer for one corner. For every exact gate v reading a data node z (the 32 nodes:
23 one-bit latches, 9 comparison/zero-test comb nodes), synthesize guards from the LCheck X-failures
(guard = "v has read event (u,j) of a node u of D v and not (u,j+1)", value = z's simulated value over v's read
interval), re-run LCheckX with them, and compute the TimedOccX.GuardTime margins against a claim built from the
latches in z's data cone: claim start A = the enable event that last closed latch l before the use, a = hi of
l's enable pin + max hi-sum along data paths l -> z; claim end B = l's next opening enable event,
b = lo of that enable pin + min lo-sum l -> z.
  start margin = Sep(A -> S) + lo'(v,u) - hi(v,z) - a        (>= 0 needed)
  end margin   = Sep(E -> B) + lo(v,z) + b - hi'(v,u)        (>= 0 needed; E = (u,j+1))
usage: data.py c"""
import sys, pickle, collections
from bisect import bisect_right
sys.path.insert(0, "/tmp/claude-0/win")
from cert import build
from lcheck import check_node, Dof
from timing import Tm, INF
DEPTH = int(sys.argv[2]) if len(sys.argv) > 2 else 8
c = int(sys.argv[1]); K = build(c, "all"); C = K["C"]; nm = C["names"]; ev = K["ev"]; eid = K["eid"]
#no timing
import functools

g = C["gates"]; EX = C["EXACT"]; DATA = C["DATA"]; hist = K["H"]["hist"]
def lo_(v, w): return K["dl"][(v, w)][0] if (v, w) in K["dl"] else 1
def hi_(v, w): return K["dl"][(v, w)][1] if (v, w) in K["dl"] else 1
def mid_(v, w): return K["dl"][(v, w)][2] if (v, w) in K["dl"] else 1
def dwin(v, z):
    for p in g[v]["pins"]:
        if p["src"] == z and p["live"]: return p["win"][c]
def flips(n): return hist[n][1] if n in hist else []
def valat(n, t): return K["valat"](n, t)
# data cone path sums l -> z (max hi, min lo), DAG through data comb
memo = {}
def paths(z):
    if z in memo: return memo[z]
    out = {}
    if z in C["LATCH"]: out[z] = (0, 0)
    elif z in g and z not in EX:
        for p in C["live"][z]:
            s = p["src"]; lo, hi, _ = p["win"][c]
            for l, (plo, phi) in paths(s).items():
                if l in out: out[l] = (min(out[l][0], plo + lo), max(out[l][1], phi + hi))
                else: out[l] = (plo + lo, phi + hi)
    memo[z] = out; return out
def ens(l):
    fb, en = C["LATCH"][l]
    return [(p, v) for p, v in en if g[l]["pins"][p]["src"] in EX]
def transp(l, t):
    """latch l transparent at t (its enable pins as read at t, mid delays)"""
    en = ens(l)
    return any(valat(g[l]["pins"][p]["src"], t - g[l]["pins"][p]["win"][c][2]) == bool(v) for p, v in en)
def latch_events(l, Tref):
    """(A, pinA, B, pinB): enable event that last closed l before Tref, and the next opening one"""
    en = ens(l)
    cand = []
    for p, v in en:
        pp = g[l]["pins"][p]; s = pp["src"]
        for k, t in enumerate(ev[s]): cand.append((t + pp["win"][c][2], s, k, p))
    cand.sort()
    if transp(l, Tref): return "open"
    A = None; B = None
    for (rt, s, k, p) in cand:
        if rt <= Tref:
            if not transp(l, rt) and transp(l, rt - 1): A = (s, k, p)
        else:
            if transp(l, rt) and not transp(l, rt - 1): B = (s, k, p); break
    return A, B
def terms(z, T, alo, ahi, depth, why):
    """claim terms for data node z's value around time T (latch outputs; open latches recursed through D)"""
    out = []
    for l, (plo, phi) in paths(z).items():
        Tref = T - (plo + phi) // 2
        st = transp(l, Tref)
        en = ens(l); cand = []
        for p, vv in en:
            pp = g[l]["pins"][p]; s_ = pp["src"]
            for k, t in enumerate(ev[s_]): cand.append((t + pp["win"][c][2], s_, k, p))
        cand.sort()
        A = None; B = None
        for (rt, s_, k, p) in cand:
            tr, tr0 = transp(l, rt), transp(l, rt - 1)
            if rt <= Tref:
                if st and tr and not tr0: A = (s_, k, p)          # last opening (open at use)
                if not st and not tr and tr0: A = (s_, k, p)      # last closing (closed at use)
            elif tr and not tr0: B = (s_, k, p); break             # next opening
        if A is None and st: why.append("latch %s open since t0" % nm[l])
        out.append(((A[0], A[1]) if A else None, ahi + phi + (g[l]["pins"][A[2]]["win"][c][1] if A else 0),
                    (B[0], B[1]) if B else None, alo + plo + (g[l]["pins"][B[2]]["win"][c][0] if B else 0)))
        if st:
            if depth >= DEPTH: why.append("depth limit at %s" % nm[l]); out.append((None, 0, None, 0)); continue
            fb = C["LATCH"][l][0]; enp = {p for p, _ in C["LATCH"][l][1]}
            for j, p in enumerate(g[l]["pins"]):
                if not p["live"] or j in fb or j in enp or p["src"] in C["const"]: continue
                if p["src"] in EX: why.append("exact D input %s" % nm[p["src"]]); continue
                lo, hi, md = p["win"][c]
                out += terms(p["src"], Tref - md, alo + plo + lo, ahi + phi + hi, depth + 1, why)
    dd = {}
    for (A, a, B, b) in out:
        key = (A, B)
        if key in dd: dd[key] = (max(dd[key][0], a), min(dd[key][1], b))
        else: dd[key] = (a, b)
    return [(A, a, B, b) for (A, B), (a, b) in dd.items()]
nUp = [0]
# ---------------- guard synthesis
res0 = {}; guards = collections.defaultdict(list); gmeta = []
nX0 = 0; nodesX = set()
for v in sorted(EX):
    if v in K["envnode"]: continue
    if not any(p["src"] in DATA for p in C["live"][v]): continue
    r = check_node(K, v, cap=10**6); res0[v] = r
    D = r["D"]
    for kind, n in r["ex"]:
        if kind != "X": continue
        nX0 += 1; nodesX.add(v)
        zs = [p["src"] for p in C["live"][v] if p["src"] in DATA]
        for z in zs:
            best = None
            for iu, u in enumerate(D):
                if n[iu] == 0: continue
                j = n[iu] - 1; ts = ev[u][j] + mid_(v, u)
                te = ev[u][j + 1] + mid_(v, u) if j + 1 < len(ev[u]) else K["H"]["tend"] + 10**6
                # z as read by v over [ts, te): constant?
                dz = mid_(v, z)
                vals = {valat(z, ts - dz)} | {valat(z, f) for f in flips(z) if ts - dz <= f < te - dz}
                if len(vals) != 1: continue
                val = vals.pop()
                cand = (ts, 0, 0, u, j, val, [])
                if best is None or cand[0] > best[0]: best = cand
            if best is not None:
                key = (v, z, best[3], best[4])
                st = (best[3], best[4]); en = (best[3], best[4] + 1) if best[4] + 1 < len(ev[best[3]]) else None
                if (st, en, best[5]) not in guards[(v, z)]:
                    guards[(v, z)].append((st, en, best[5]))
                    gmeta.append((best[0], best[1], best[2], v, z, st, en, best[5], best[6]))
            else:
                gmeta.append((None, None, None, v, z, None, None, None, ["no stable interval found"]))
# ---------------- LCheckX with guards
nX1 = 0; other1 = collections.Counter()
for v in res0:
    r = check_node(K, v, guards=guards, cap=10**6)
    for kind, n in r["ex"]:
        if kind == "X": nX1 += 1
        else: other1[kind] += 1
print("guards", sum(len(x) for x in guards.values()), "X before", nX0, "after", nX1, dict(other1))
pickle.dump(dict(gmeta=gmeta, guards=dict(guards)), open("/tmp/claude-0/win/data_c%d%s.pkl" % (c, __import__("os").environ.get("PAIR", "")), "wb"))
