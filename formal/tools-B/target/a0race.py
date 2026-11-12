#!/usr/bin/env python3
"""Shard B (UNTRUSTED): from a baseline dump, per arbiter, closest approaches at ustate's pins of
(1) a request edge to A0's fall while the OTHER request is high (bd_arb.v: the held arbiter's evaluation
window opens at A0's fall; a request edge there is the runt condition), and
(2) opposite-sense request edges (one falls, the other rises) -- harmless only if no set/reset pulse.
usage: a0race.py NET.json ARBS.json BND.json DUMP.json"""
import json, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
dump = sys.argv[4]
src = open(os.path.join(HERE, "adv.py")).read()
src = src[:src.index('base, res0 = run({}, "base")')]
sys.argv = sys.argv[:4] + ["0,1"]
ns = {"__file__": os.path.join(HERE, "adv.py")}
exec(compile(src, "adv.py", "exec"), ns)
roles, A, g, val_at = ns["roles"], ns["A"], ns["g"], ns["val_at"]
D = json.load(open(dump))["nodes"]
def edges(n):
    v0, ts = D.get(str(n), [False, []]); v = v0; out = []
    for t in ts:
        v = not v; out.append((t, v))
    return out
for k, a in enumerate(A):
    R = roles(a)
    a0f = [t for t, v in edges(R["a0"]) if not v and t > 20000]
    best1 = None
    for name, me, other in (("r1", R["r1"], R["r2"]), ("r2", R["r2"], R["r1"])):
        for t, v in edges(me):
            if t <= 20000: continue
            for ta in a0f:
                if val_at(D, other, max(t, ta)) and (best1 is None or abs(t - ta) < best1[0]):
                    best1 = (abs(t - ta), name, "rise" if v else "fall", t, ta)
    best2 = None
    for t1, v1 in edges(R["r1"]):
        for t2, v2 in edges(R["r2"]):
            if t1 > 20000 and t2 > 20000 and v1 != v2 and (best2 is None or abs(t1 - t2) < best2[0]):
                best2 = (abs(t1 - t2), "r1 " + ("rise" if v1 else "fall"), t1, "r2 " + ("rise" if v2 else "fall"), t2)
    print("arb %d %s: req edge vs A0 fall (other high): %s | opposite-sense request edges: %s" % (k, g[R["q"]]["name"], best1, best2))
