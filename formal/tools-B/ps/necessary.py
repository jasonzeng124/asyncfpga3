#!/usr/bin/env python3
"""Shard B (UNTRUSTED): is each hop of a back-traced causal path a NECESSARY input of that gate's transition?
For hop (gate n, pin i) with n flipping at t: the gate's reads at t (mid-window delays, from the dump) give the new
output; with pin i's read replaced by its value just before its last flip (the other reads unchanged), does the gate
still produce its OLD output? If yes for every hop, the end event cannot occur in that run's event order before the
path's delay after the start. usage: necessary.py NET.json DUMP.json ARCS.json [corner]"""
import json, sys
from bisect import bisect_right
N = json.load(open(sys.argv[1])); g = N["gates"]; D = json.load(open(sys.argv[2]))["nodes"]; A = json.load(open(sys.argv[3]))
c = float(sys.argv[4]) if len(sys.argv) > 4 else 0.5
def dmid(e):
    lo = (1 - c) * e["fmin"] + c * e["smin"]; hi = (1 - c) * e["fmax"] + c * e["smax"]; return int(round((lo + hi) / 2))
def hist(n): return D.get(str(n), [False, []])
def val(n, t):
    v0, ts = hist(n); return v0 ^ (bisect_right(ts, t) % 2 == 1) if t >= 0 else v0
def out(G, bits):
    a = sum(1 << i for i, b in enumerate(bits) if b); return (G["init"] >> a) & 1
# walk the path from the node's own flip forward: path is listed end-first, so reverse
path = [tuple(x) for x in A["path"]][::-1]
gi = A["node"]
t = None
# find each hop's flip time by following the dump forward from the node's flip that starts the episode
ts_node = hist(gi)[1]
res = []
cur_t = None
for idx, (n, pin) in enumerate(path):
    G = g[n]; src = G["ins"][pin]
    # the source's flip feeding this hop: the latest src flip; the gate's flip right after src flip + d
    if cur_t is None:
        # src of the first hop is the node itself (or a copy of it); take the node flip before the first gate flip
        pass
    d = dmid(G["arcs"][pin])
    ts_src = hist(src)[1]
    ts_n = hist(n)[1]
    if cur_t is None:
        cand = [x for x in ts_n]
    else:
        cand = [x for x in ts_n if x >= cur_t]
    if not cand: res.append((idx, n, pin, "no flip")); break
    tn = cand[0] if cur_t is not None else None
    if tn is None:
        # first hop: pick the gate flip whose src flip (at tn - d) exists
        tn = next(x for x in ts_n if bisect_right(ts_src, x - d) and val(src, x - d) != val(src, x - d - 1) or True)
    reads = [val(m, tn - dmid(G["arcs"][q])) for q, m in enumerate(G["ins"])]
    new = out(G, reads); old = val(n, tn - 1)
    alt = list(reads); alt[pin] = not alt[pin]
    nec = (out(G, alt) == old) and new != old
    res.append((idx, n, pin, G["k"], tn, nec))
    cur_t = tn
for r in res: print(r)
print("all necessary:", all(r[-1] is True for r in res if len(r) == 6), "hops", len(res))
