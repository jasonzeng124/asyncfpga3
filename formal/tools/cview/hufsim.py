#!/usr/bin/env python3
"""Shard C (UNTRUSTED explorer): THE target as an abstract Huffman machine.
State = the storage nodes (logic gates whose own output is a pin source in the collapsed view);
all other logic is evaluated with zero delay (SpecLoop.settle_value: what the timed circuit settles
to). One step fires ONE excited storage node chosen at random (speed-independent semantics). The
environment follows A's sim.py sequential protocol (shared request; out0/pend acks follow their
requests). Reports results, and every persistence violation (a storage node excited and then
disabled without firing): the places where the design relies on timing, not on order alone.
usage: hufsim.py net.json boundary.json --pairs a,b [a,b ...] [--seed S] [--runs R]"""
import json, sys, random, argparse, collections, heapq
ap = argparse.ArgumentParser(); ap.add_argument("net"); ap.add_argument("bnd")
ap.add_argument("--pairs", nargs="+", required=True); ap.add_argument("--seed", type=int, default=1)
ap.add_argument("--runs", type=int, default=1); ap.add_argument("--maxsteps", type=int, default=400000)
ap.add_argument("--names", default=None)
ap.add_argument("--latch-first", action="store_true", help="excited latch-like storage nodes (an enable pin, one value of which makes the feedback irrelevant) fire before any other storage node (relative timing: bundling)")
a = ap.parse_args()
net = json.load(open(a.net)); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
BJ = json.load(open(a.bnd)); B = BJ["boundary"]; ENV = set(idx[x] for x in BJ["env"])
nb = lambda k: idx[B[k]]
def is_copy(g): return g["k"] == 1 and g["init"] == 2
cm = {i: g["ins"][0] for i, g in enumerate(G) if is_copy(g) and i not in ENV}
def src(u):
    while u in cm: u = cm[u]
    return u
logic = [i for i, g in enumerate(G) if not is_copy(g) and i not in ENV]
pins = {i: [src(u) for u in G[i]["ins"]] for i in logic}
stor = {i for i in logic if i in pins[i]}
comb = [i for i in logic if i not in stor]
def dep(g, j):
    k, I = g["k"], g["init"]
    return any(((I >> x) & 1) != ((I >> (x ^ (1 << j))) & 1) for x in range(1 << k))
def latch_like(i):
    g = G[i]; k, I = g["k"], g["init"]
    fb = [j for j, s in enumerate(pins[i]) if s == i and dep(g, j)]
    if not fb: return False
    fbj = fb[0]
    for p in range(k):
        if p == fbj or not dep(g, p) or pins[i][p] in ENV or pins[i][p] >= len(G): continue
        for v in (0, 1):
            if all(((I >> x) & 1) == ((I >> (x ^ (1 << fbj))) & 1) for x in range(1 << k) if ((x >> p) & 1) == v):
                return True
    return False
LATCH = {i for i in stor if latch_like(i)}
print("storage", len(stor), "latch-like", len(LATCH), file=sys.stderr)
fan = collections.defaultdict(list)
for i in logic:
    for s in set(pins[i]): fan[s].append(i)
# ranks of comb
rank = {}; indeg = collections.Counter(); succ = collections.defaultdict(list)
for i in comb:
    for s in pins[i]:
        if s in pins and s not in stor: succ[s].append(i); indeg[i] += 1
q = [i for i in comb if indeg[i] == 0]
for i in q: rank[i] = 0
while q:
    v = q.pop()
    for w in succ[v]:
        rank[w] = max(rank.get(w, 0), rank[v] + 1); indeg[w] -= 1
        if indeg[w] == 0: q.append(w)
def f(i, val):
    g = G[i]; ad = 0
    for j, s in enumerate(pins[i]):
        if val.get(s, False): ad |= 1 << j
    return bool((g["init"] >> ad) & 1)
names = {}
if a.names:
    import re
    bel = json.load(open(a.names))
    def cell(nm):
        m = re.match(r'(SLICE_X\d+Y\d+)\.([A-D])([56])$', nm)
        return bel.get(f"{m.group(1)}/{m.group(2)}{m.group(3)}LUT", nm) if m else nm
else:
    cell = lambda nm: nm
def run(seed):
    rnd = random.Random(seed); val = collections.defaultdict(bool)
    def settle(changed):
        h = [(rank[w], w) for c in changed for w in fan[c] if w in rank]; heapq.heapify(h); seen = set()
        while h:
            r, w = heapq.heappop(h)
            if w in seen: continue
            seen.add(w); nv = f(w, val)
            if nv != val[w]:
                val[w] = nv
                for x in fan[w]:
                    if x in rank and x not in seen: heapq.heappush(h, (rank[x], x))
    def setenv(n, v):
        if val[n] != v: val[n] = v; settle([n])
    # constants and initial evaluation
    for w in sorted(comb, key=lambda w: rank[w]): val[w] = f(w, val)
    setenv(nb("rst"), True)
    excited = lambda: [s for s in stor if f(s, val) != val[s]]
    def fire_until_stable(limit=200000):
        for _ in range(limit):
            ex = excited()
            if not ex: return True
            s = rnd.choice(ex); val[s] = not val[s]; settle([s])
        return False
    if not fire_until_stable(): return ("reset did not settle",)
    setenv(nb("rst"), False); fire_until_stable()
    ctrl = sorted(stor - LATCH)
    idle0 = {s: val[s] for s in ctrl}
    run.idle_diffs = []
    pairs = [tuple(int(x, 0) for x in p.split(",")) for p in a.pairs]
    k = 0; results = []; req = nb("req"); acks = [nb("a_ack"), nb("b_ack"), nb("start_ack")]
    oR, oA, pA = nb("out0_req"), nb("out0_ack"), nb("pend_ack")
    pend_req = req   # the pend channel's request is the shared input request (sim.py)
    def setbus(key, v):
        for bit, nm in enumerate(B[key]):
            n = idx[nm]
            if n in ENV: setenv(n, bool((v >> bit) & 1))
    if pairs: setbus("a_data", pairs[0][0]); setbus("b_data", pairs[0][1])
    waiting_out = False; persist = collections.Counter(); prev_ex = set(); steps = 0
    while steps < a.maxsteps:
        # environment moves (instantaneous, between storage firings)
        A = [val[x] for x in acks]
        if not val[req] and not any(A) and k < len(pairs) and not waiting_out:
            setbus("a_data", pairs[k][0]); setbus("b_data", pairs[k][1]); setenv(req, True)
        elif val[req] and all(A): setenv(req, False); waiting_out = True
        if val[oR] and not val[oA]:
            results.append(sum((1 << b) for b, nm in enumerate(B["out0_data"]) if val[idx[nm]])); setenv(oA, True)
        elif not val[oR] and val[oA]:
            setenv(oA, False); k += 1; waiting_out = False
            fire_until_stable_ctrl = None
        if val[pend_req] != val[pA] and False: pass
        setenv(pA, val[pend_req])
        ex = set(excited())
        for s in prev_ex - ex:
            if not hasattr(run, "fired") or s != run.fired: persist[s] += 1
        if not ex:
            if waiting_out is False and not val[req] and not val[oA]:
                d = [N[s] for s in ctrl if val[s] != idle0[s]]
                if d not in run.idle_diffs: run.idle_diffs.append(d)
            if k >= len(pairs) and not val[oR] and not val[oA]: break
            return ("deadlock", results, k, persist)
        pool = sorted(ex & LATCH) if (a.latch_first and ex & LATCH) else sorted(ex)
        s = rnd.choice(pool); run.fired = s; val[s] = not val[s]; settle([s]); steps += 1
        prev_ex = ex - {s}
    return ("ok" if steps < a.maxsteps else "maxsteps", results, steps, persist)
import math
tot = collections.Counter()
for r in range(a.runs):
    res = run(a.seed + r)
    exp = [math.gcd(x, y) for x, y in (tuple(int(v, 0) for v in p.split(",")) for p in a.pairs)]
    print("idle-state differences seen at quiescent points (control storage):", [len(d) for d in run.idle_diffs], (run.idle_diffs[-1][:5] if run.idle_diffs else None))
    print("run", r, res[0], "results", res[1] if len(res) > 1 else None, "expected", exp, "steps", res[2] if len(res) > 2 else None)
    if len(res) > 3: tot.update(res[3])
print("persistence violations (node: count) over all runs:", len(tot))
for n, c in tot.most_common(25): print(" ", c, cell(N[n]))
