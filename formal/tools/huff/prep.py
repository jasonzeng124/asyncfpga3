#!/usr/bin/env python3
"""Shard C (UNTRUSTED): flatten THE target's collapsed view for the exhaustive Huffman explorer (huffx.cpp).
Same abstraction as tools/cview/hufsim.py: storage nodes (a logic gate reading its own output) are the state,
other logic is zero-delay; latch-like storage nodes (an enable value makes the feedback irrelevant) are
the data latches. Output: a whitespace text file read by huffx.
usage: prep.py net.json bnd.json out.txt"""
import json, sys, collections
net = json.load(open(sys.argv[1])); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
BJ = json.load(open(sys.argv[2])); B = BJ["boundary"]; ENV = set(idx[x] for x in BJ["env"])
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
rank = {}; indeg = collections.Counter(); succ = collections.defaultdict(list)
for i in comb:
    for s in pins[i]:
        if s in pins and s not in stor: succ[s].append(i); indeg[i] += 1
q = [i for i in comb if indeg[i] == 0]
for i in q: rank[i] = 0
order = []
while q:
    v = q.pop(); order.append(v)
    for w in succ[v]:
        rank[w] = max(rank.get(w, 0), rank[v] + 1); indeg[w] -= 1
        if indeg[w] == 0: q.append(w)
assert len(order) == len(comb)
# compact ids: every node that is a pin source or a gate output or a boundary node
used = set(logic) | set(s for i in logic for s in pins[i]) | ENV
for k in ("rst", "req", "a_ack", "b_ack", "start_ack", "out0_req", "out0_ack", "pend_ack"): used.add(src(idx[B[k]]) if idx[B[k]] not in ENV else idx[B[k]])
for k in ("a_data", "b_data", "out0_data"):
    for nm in B[k]: used.add(src(idx[nm]) if idx[nm] not in ENV else idx[nm])
ids = {u: n for n, u in enumerate(sorted(used))}
out = open(sys.argv[3], "w")
out.write("nodes %d\n" % len(ids))
for u in sorted(used): out.write("%s\n" % N[u])
def gl(i): return "%d %d %s %s" % (ids[i], G[i]["k"], " ".join(str(ids[s]) for s in pins[i]), format(G[i]["init"], "x"))
out.write("comb %d\n" % len(order))
for i in order: out.write(gl(i) + "\n")
st = sorted(stor)
out.write("stor %d\n" % len(st))
for i in st: out.write(gl(i) + " %d\n" % (1 if i in LATCH else 0))
def bn(k):
    u = idx[B[k]]; return ids[u if u in ENV else src(u)]
out.write("bnd %s\n" % " ".join("%s=%d" % (k, bn(k)) for k in ("rst", "req", "a_ack", "b_ack", "start_ack", "out0_req", "out0_ack", "pend_ack")))
for k in ("a_data", "b_data", "out0_data"):
    out.write("%s %s\n" % (k, " ".join(str(ids[idx[nm] if idx[nm] in ENV else src(idx[nm])]) for nm in B[k])))
out.write("env %s\n" % " ".join(str(ids[u]) for u in sorted(ENV)))
print("prep: %d ids, %d comb (depth %d), %d storage (%d latch-like)" % (len(ids), len(order), max(rank.values()), len(st), len(LATCH)))
