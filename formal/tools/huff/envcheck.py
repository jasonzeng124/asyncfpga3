#!/usr/bin/env python3
"""Shard C (UNTRUSTED): check a dumped run's boundary against Spec.Env (+ SeqEnv) clause by clause, measure the
smallest T for which Spec.ArbOK T holds, and report Correct's out0 liveness.
usage: envcheck.py net.json bnd.json dump.json R su dout PAIRS..."""
import json, sys, bisect, math
net = json.load(open(sys.argv[1])); N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
BJ = json.load(open(sys.argv[2])); B = BJ["boundary"]
D = json.load(open(sys.argv[3])); R, su, dout = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
pairs = [tuple(int(x, 0) for x in p.split(",")) for p in sys.argv[7:]]
sig = {int(k): (bool(v[0]), v[1]) for k, v in D["nodes"].items()}
def fl(n): return sig.get(idx[n] if isinstance(n, str) else n, (False, []))
def val(n, t):
    v0, f = fl(n); return v0 ^ (bisect.bisect_right(f, t) % 2 == 1)
def rises(n, t):  # rising edges at times in (R, t]
    v0, f = fl(n); return sum(1 for i, s in enumerate(f) if R < s <= t and (v0 ^ (i % 2 == 0)))
ok = True
def need(c, msg):
    global ok
    if not c: ok = False; print("FAIL:", msg)
req, rst = B["req"], B["rst"]
need(all(val(rst, t) for t in [0, R - 1]) and not val(rst, R) and len(fl(rst)[1]) == 1 and fl(rst)[1][0] == R and fl(rst)[0], "reset high on [0,R), low after")
need(all(not val(req, t) for t in [0, R]) and all(s > R for s in fl(req)[1]), "req low on [0,R]")
for ack in ("a_ack", "b_ack", "start_ack"):
    a = B[ack]
    for i, s in enumerate(fl(req)[1]):
        up = not val(req, s - 1)
        need(not val(a, s - 1) if up else val(a, s - 1), "ReqMoves %s at %d" % (ack, s))
need(rises(req, D["tend"]) <= len(pairs), "at most n rises")
need(not val(req, D["tend"]), "req low at end (ReqLive: no request left pending)")
def bus(key, t): return sum((1 << i) for i, nm in enumerate(B[key]) if val(nm, t))
# data: during [rise - su, rise] and whenever req or ack is high (after the first rise): pair k
for key, ack, j in (("a_data", "a_ack", 0), ("b_data", "b_ack", 1)):
    pts = sorted(set([R] + [s for n in [req, B[ack]] + B[key] for s in fl(n)[1]] + [s - 1 for n in [req, B[ack]] + B[key] for s in fl(n)[1]]))
    for t in pts:
        if t < R: continue
        k = rises(req, t)
        if (val(req, t) or val(B[ack], t)) and k >= 1:
            need(bus(key, t) == pairs[k - 1][j], "data %s at %d: %d vs pair %d" % (key, t, bus(key, t), k - 1))
    for s in fl(req)[1]:
        if not val(req, s - 1):
            k = rises(req, s)
            for t in range(max(R, s - su), s + 1):
                need(bus(key, t) == pairs[k - 1][j], "setup %s at %d" % (key, t))
for ch, rq in (("out0_ack", B["out0_req"]), ("pend_ack", req)):
    a = B[ch]
    need(all(s > R for s in fl(a)[1]) and not fl(a)[0], "%s low on [0,R]" % ch)
    for i, s in enumerate(fl(a)[1]):
        up = not val(a, s - 1)
        need(val(rq, s - 1) if up else not val(rq, s - 1), "AckMoves %s at %d" % (ch, s))
        if up: need(all(val(rq, t) for t in range(s - dout, s + 1)), "Δo %s at %d" % (ch, s))
    need(val(a, D["tend"]) == val(rq, D["tend"]), "AckLive %s (ack follows req at the end)" % ch)
# SeqEnv: the (k+1)-th req rise only after out0 acked k times and out0 req/ack low
for s in fl(req)[1]:
    if not val(req, s - 1):
        k = rises(req, s - 1)
        need(k <= rises(B["out0_ack"], s - 1) and not val(B["out0_req"], s - 1) and not val(B["out0_ack"], s - 1), "SeqEnv at %d" % s)
print("Env + SeqEnv:", "OK" if ok else "VIOLATED")
# ArbOK: smallest T: every q flip at s has an input flip in [s - T, s] (q constant once inputs constant for T)
Tmin = 0
for a in BJ["arbs"]:
    q = a["q"]; ins = [s for n in a["ins"] for s in fl(n)[1]]
    for s in fl(q)[1]:
        prev = [x for x in ins if x <= s - 1]
        lag = s - max(prev) if prev else s
        Tmin = max(Tmin, lag)
print("ArbOK T holds for every T >= %d ps (largest lag from a state-LUT input change to a state change)" % Tmin)
o = B["out0_req"]
print("out0 rises:", rises(o, D["tend"]), "of", len(pairs), "owed; out0_req at end:", val(o, D["tend"]), "; quiescent end:", D["tend"])
