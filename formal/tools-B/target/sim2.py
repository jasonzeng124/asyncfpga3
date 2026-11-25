#!/usr/bin/env python3
"""Shard B: an INDEPENDENT re-implementation (not shard A's code) of the Spec gate relation with constant
read delays (transport), used to cross-check simb.py runs. The environment is REPLAYED: every node that no
cone gate drives takes its waveform from a reference dump. Delays: same window/posmap rule as simb.py.
Output: compares every node's flip list with the reference dump up to TMAX.
usage: sim2.py NET.json BND.json REFDUMP.json CORNER KAPPA POSMAP TMAX [TFROM]"""
import json, sys, heapq
from bisect import bisect_right
NETF, BNDF, REF, C, K, PMF, TMAX = sys.argv[1:8]; c = float(C); kap = float(K); TMAX = int(TMAX)
TFROM = int(sys.argv[8]) if len(sys.argv) > 8 else 25000
N = json.load(open(NETF)); g = N["gates"]; names = N["nodes"]; idx = {n: i for i, n in enumerate(names)}
B = json.load(open(BNDF)); ENV = set(idx[x] for x in B["env"]); ref = json.load(open(REF))["nodes"]
raw = json.load(open(PMF)) if PMF != "-" else {}
pm_g = {int(k): v for k, v in raw.items() if ":" not in k}
pm_p = {tuple(map(int, k.split(":"))): v for k, v in raw.items() if ":" in k}
def delay(e, gi, pin):
    lo = (1 - c) * e["fmin"] + c * e["smin"]; hi = (1 - c) * e["fmax"] + c * e["smax"]
    pos = pm_p.get((gi, pin), pm_g.get(gi, 0.5))
    if pos == -1: d = max((1 - kap) * lo, e["fmin"]); return int(-(-d // 1))
    if pos == 2: d = min((1 + kap) * hi, e["smax"]); return int(d // 1)
    return int(round(lo + pos * (hi - lo)))
# the cone: gates reachable backwards from the boundary outputs, not through env nodes (as sim.py)
bd = B["boundary"]
outs = [idx[bd[k]] for k in ("a_ack", "b_ack", "start_ack", "out0_req")] + [idx[x] for x in bd["out0_data"]]
cone, todo, seen = set(), list(outs), set(outs)
while todo:
    n = todo.pop()
    if n in ENV or n >= len(g): continue
    cone.add(n)
    for i in g[n]["ins"]:
        if i not in seen: seen.add(i); todo.append(i)
D = {gi: [delay(e, gi, p) for p, e in enumerate(g[gi]["arcs"])] for gi in cone}
readers = {}
for gi in cone:
    for p, n in enumerate(g[gi]["ins"]): readers.setdefault(n, []).append((gi, D[gi][p]))
# node waveforms: initial value + flip times
v0 = {}; fl = {}
for n in seen | cone:
    if n in cone: v0[n] = False; fl[n] = []
    else:
        r = ref.get(str(n), [False, []]); v0[n] = r[0]; fl[n] = [t for t in r[1] if t <= TMAX + 10**6]
def val(n, t):
    if t < 0: return v0.get(n, False)
    return v0.get(n, False) ^ (bisect_right(fl.get(n, []), t) % 2 == 1)
Q = []
def push(t, gi): heapq.heappush(Q, (t, gi))
for gi in cone: push(0, gi)
for n in seen - cone:
    for t in fl.get(n, []):
        for gi, d in readers.get(n, []): push(t + d, gi)
while Q:
    t, gi = heapq.heappop(Q)
    if t > TMAX: break
    G = g[gi]; a = 0
    for p, n in enumerate(G["ins"]):
        if val(n, t - D[gi][p]): a |= 1 << p
    v = bool((G["init"] >> a) & 1)
    if v != val(gi, t):
        f = fl[gi]
        if f and f[-1] == t: f.pop()          # two changes at one instant cancel
        else: f.append(t)
        for r, d in readers.get(gi, []): push(t + d, r)
    # initial value: a gate evaluated at 0 sets its power-up value
# compare
diff = 0; checked = 0
for gi in cone:
    # power-up conventions differ (shard A's reads before 0 depend on event order); compare after the reset
    mine = [t for t in fl[gi] if TFROM < t <= TMAX]
    theirs = [t for t in ref.get(str(gi), [False, []])[1] if TFROM < t <= TMAX]
    checked += 1
    if mine != theirs:
        diff += 1
        if diff <= 5: print("DIFF", g[gi]["name"], mine[:8], theirs[:8])
print("sim2: cone %d gates, compared %d, differing %d (up to %d ps)" % (len(cone), checked, diff, TMAX))
