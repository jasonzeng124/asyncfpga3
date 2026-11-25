#!/usr/bin/env python3
"""Shard C helper (UNTRUSTED): transport-delay simulation of the COLLAPSED kernel cone (model.pkl), every pin at the
composite midpoint delay of corner c (sum of per-arc integer midpoints; inside [lo, hi]); env as simadv.py
(SeqEnv, one pair, operands set at time 1, rst high on [0, R), req rises 1 ps after all acks seen low, out0/pend
acks follow their request after dout). Writes hist_c<c>.pkl: {node: (v0, [flip times])}.
usage: sim.py c A B [R] [dout]"""
import sys, heapq, pickle, collections, math
from bisect import bisect_right
sys.path.insert(0, "/tmp/claude-0/r1c")
from classify import load
c = int(sys.argv[1]); A = int(sys.argv[2]); Bv = int(sys.argv[3])
R = int(sys.argv[4]) if len(sys.argv) > 4 else 40000
dout = int(sys.argv[5]) if len(sys.argv) > 5 else 3000
C = load(); gates = C["gates"]; bs = C["bs"]; names = C["names"]
G = {}
readers = collections.defaultdict(list)
for n, g in gates.items():
    ins = [p["src"] for p in g["pins"]]; ds = [p["win"][c][2] for p in g["pins"]]
    G[n] = (g["k"], g["init"], ins, ds)
    for j, (s, d) in enumerate(zip(ins, ds)): readers[s].append((n, d))
ht = collections.defaultdict(lambda: [0]); hv = collections.defaultdict(lambda: [False])
def val(n, t):
    ts = ht[n]; return hv[n][bisect_right(ts, t) - 1] if t >= 0 else hv[n][0]
def setv(n, t, v):
    ts, vs = ht[n], hv[n]
    if ts[-1] == t:
        if len(ts) > 1 and vs[-2] == v: ts.pop(); vs.pop(); return True
        if vs[-1] != v: vs[-1] = v; return True
        return False
    assert t > ts[-1]
    if vs[-1] == v: return False
    ts.append(t); vs.append(v); return True
Q = []; seq = [0]
def push(t, pri, x):
    seq[0] += 1; heapq.heappush(Q, (t, pri, seq[0], x))
def changed(n, t):
    for g, d in readers.get(n, ()): push(t + d, 0, g)
def ev(n, t):
    k, init, ins, ds = G[n]
    a = 0
    for i in range(k):
        if val(ins[i], t - ds[i]): a |= 1 << i
    if setv(n, t, bool(init >> a & 1)): changed(n, t)
def env_set(t, n, v): push(t, -1, (n, v))
def bus(key, t, vals):
    want = {}
    for i, n in enumerate(bs[key]): want[n] = bool(vals >> i & 1)
    for n, b in want.items(): env_set(t, n, b)
rst, req = bs["rst"], bs["req"]
aA, aB, aS, oR, oA, eA = (bs[k] for k in ("a_ack", "b_ack", "start_ack", "out0_req", "out0_ack", "pend_ack"))
env_set(0, rst, True); env_set(R, rst, False)
bus("a_data", 1, A); bus("b_data", 1, Bv)
for n in G: push(0, 0, n)
offered = False; reqs = False; outp = False; pend = False; outs = []; tend = 0
while Q:
    t, pri, _, x = heapq.heappop(Q)
    if t > 50_000_000: print("TIMEOUT"); break
    if pri == -1:
        n, v = x
        if setv(n, t, v): changed(n, t)
    elif pri == 0: ev(x, t)
    tend = t
    if Q and Q[0][0] == t: continue
    if t < R: continue
    acks = (val(aA, t), val(aB, t), val(aS, t))
    if not offered and not reqs and not any(acks):
        env_set(t + 1, req, True); reqs = True; offered = True
    elif reqs and all(acks) and val(req, t):
        env_set(t + 1, req, False); reqs = False
    r0 = val(oR, t)
    if r0 and not val(oA, t) and not outp:
        outp = True; env_set(t + dout, oA, True); push(t + dout, -2, None)
        smp = t + dout - 1
        outs.append(smp)
    if not r0 and val(oA, t) and outp:
        outp = False; env_set(t + dout, oA, False)
    pr = val(req, t)
    if pr != pend:
        pend = pr; env_set(t + dout, eA, pr)
OD = bs["out0_data"]
res = [sum((1 << i) for i, n in enumerate(OD) if val(n, s)) for s in outs]
print("corner %d: tend %d, outputs %s (want %d)" % (c, tend, res, math.gcd(A, Bv)))
lastpre = max((ts[-1] for n, ts in ht.items() if len(ts) > 1 and ts[-1] < R and n in C["EXACT"]), default=0)
lastpre_all = max((max([x for x in ts[1:] if x < R], default=0) for n, ts in ht.items()), default=0)
print("last change before R: exact %d, any %d (R = %d)" % (lastpre, lastpre_all, R))
pickle.dump(dict(c=c, R=R, dout=dout, A=A, B=Bv, tend=tend, outs=outs, res=res,
                 hist={n: (hv[n][0], ht[n][1:]) for n in ht}), open("/tmp/claude-0/r1c/hist_c%d.pkl" % c, "wb"))
