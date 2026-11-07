#!/usr/bin/env python3
"""Shard C (UNTRUSTED explorer): is THE target's post-reset idle state stable whatever the
(unreset) data latches hold? Ternary (Kleene 0/1/X) evaluation: reset-forced storage nodes at their
reset values, every other storage node X, env idle (rst = 0, req = 0, out0/pend acks 0, data X),
logic evaluated to a fixed point. Reports which storage nodes / boundary outputs are determined
and whether each determined storage node is CONFIRMED (its INIT at the ternary inputs equals its
value whatever the X inputs are)."""
import json, sys, collections
net = json.load(open(sys.argv[1])); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
BJ = json.load(open(sys.argv[2])); B = BJ["boundary"]; ENV = set(idx[x] for x in BJ["env"])
cm = {i: g["ins"][0] for i, g in enumerate(G) if g["k"] == 1 and g["init"] == 2 and i not in ENV}
def src(u):
    while u in cm: u = cm[u]
    return u
logic = [i for i, g in enumerate(G) if i not in cm and i not in ENV and not (g["k"] == 1 and g["init"] == 2)]
pins = {i: [src(u) for u in G[i]["ins"]] for i in logic}
stor = {i for i in logic if i in pins[i]}
rst = idx[B["rst"]]
def dep(g, j):
    k, I = g["k"], g["init"]; return any(((I >> a) & 1) != ((I >> (a ^ (1 << j))) & 1) for a in range(1 << k))
forced = {}
for s in stor:
    g = G[s]; rj = [j for j, p in enumerate(pins[s]) if p == rst and dep(g, j)]
    if rj:
        j = rj[0]; vals = set(((g["init"] >> a) & 1) for a in range(1 << g["k"]) if (a >> j) & 1)
        if len(vals) == 1: forced[s] = vals.pop()
X = None
def tern(i, val):
    g = G[i]; k = g["k"]; I = g["init"]; known = 0; mask = 0
    for j, s in enumerate(pins[i]):
        v = val.get(s, X)
        if v is X: mask |= 1 << j
        elif v: known |= 1 << j
    outs = set()
    sub = mask
    while True:
        outs.add((I >> (known | sub)) & 1)
        if len(outs) > 1: return X
        if sub == 0: break
        sub = (sub - 1) & mask
    return outs.pop()
val = {}
for n in ENV: val[n] = X
for nm in ["rst", "req", "out0_ack", "pend_ack"]: val[idx[B[nm]]] = 0
for s in stor: val[s] = forced.get(s, X)
comb = [i for i in logic if i not in stor]
for it in range(200):
    ch = 0
    for i in comb:
        v = tern(i, val)
        if val.get(i, "u") != v: val[i] = v; ch += 1
    if ch == 0: break
print("fixpoint after", it, "sweeps")
conf = collections.Counter(); bad = []
for s in stor:
    if s in forced:
        v = tern(s, val)
        conf["forced+confirmed" if v == forced[s] else ("forced but X" if v is X else "forced but FLIPS")] += 1
        if v != forced[s]: bad.append((N[s], v))
    else:
        conf["unreset"] += 1
print(conf, bad[:10])
for nm in ["a_ack", "b_ack", "start_ack", "out0_req"]:
    print(nm, val.get(idx[B[nm]]))
# start-up transient: fire every determined, excited storage node; repeat to a fixed point
rounds = 0
while True:
    for it in range(200):
        ch = 0
        for i in comb:
            v = tern(i, val)
            if val.get(i, "u") != v: val[i] = v; ch += 1
        if ch == 0: break
    flips = []
    for s in stor:
        if val[s] is X: continue
        v = tern(s, val)
        if v is X: print("  storage", N[s], "becomes X"); flips.append((s, X))
        elif v != val[s]: flips.append((s, v))
    if not flips: break
    rounds += 1
    print("round", rounds, "fires", len(flips), [N[s] for s, _ in flips][:6])
    for s, v in flips: val[s] = v
    if rounds > 50: print("no fixpoint"); break
print("idle fixpoint after", rounds, "rounds; boundary:", {nm: val.get(idx[B[nm]]) for nm in ["a_ack", "b_ack", "start_ack", "out0_req"]})
print("undetermined control storage:", sum(1 for s in forced if val[s] is X))
# self-confirming island around the boundary outputs (values from the idle fixpoint)
def forces(i, assign):
    """INIT of gate i gives one value for every completion of the partial assignment {pin: bit}."""
    g = G[i]; k = g["k"]; I = g["init"]; outs = set()
    free = [j for j in range(k) if j not in assign]
    base = sum(1 << j for j, b in assign.items() if b)
    for m in range(1 << len(free)):
        a = base | sum(1 << free[t] for t in range(len(free)) if (m >> t) & 1)
        outs.add((I >> a) & 1)
        if len(outs) > 1: return None
    return outs.pop()
island = {}; todo = [idx[B[nm]] for nm in ["a_ack", "b_ack", "start_ack", "out0_req"]]
envfixed = {idx[B["rst"]]: 0, idx[B["req"]]: 0, idx[B["out0_ack"]]: 0, idx[B["pend_ack"]]: 0}
while todo:
    w = todo.pop()
    if w in island: continue
    if w in envfixed: island[w] = ("env", envfixed[w], []); continue
    if w not in pins: island[w] = ("UNDET", None, []); continue
    v = val[w]
    if v is X: island[w] = ("UNDET", None, []); continue
    assign = {j: val[s] for j, s in enumerate(pins[w]) if val.get(s, X) is not X}
    if forces(w, assign) != v: island[w] = ("NOTFORCED", v, []); continue
    for j in sorted(assign):          # greedy minimisation
        t = dict(assign); del t[j]
        if forces(w, t) == v: assign = t
    island[w] = ("gate", v, sorted(assign))
    for j in assign: todo.append(pins[w][j])
kinds = collections.Counter(("stor" if w in stor else ("env" if island[w][0] == "env" else "comb")) + ":" + island[w][0] for w in island)
print("island size", len(island), kinds)
bad = [N[w] for w in island if island[w][0] in ("UNDET", "NOTFORCED")]
print("problems:", bad[:10])
json.dump({str(w): [island[w][0], island[w][1], island[w][2]] for w in island}, open("/tmp/claude-0/ps/island.json", "w"))
chg = [N[w] for w in island if w in stor and w in forced and forced[w] != island[w][1]]
unres = [N[w] for w in island if w in stor and w not in forced]
print("island storage nodes whose idle value differs from reset value:", chg, "; island storage without reset forcing:", unres[:5], len(unres))
