#!/usr/bin/env python3
"""reset_x.py (audit T15): three-valued (0/1/X) zero-delay fixpoint of the auditor's own decode with the kernel reset
node held at 1 and EVERY other environment node and every gate output starting X (unknown). A gate's output becomes
definite only if all completions of its X inputs give the same value (Kleene, monotone from X). Reports the values
the boundary handshake outputs settle to.   python3 -I reset_x.py NET.json BND.json [RST_VALUE]"""
import json, sys, collections, itertools
N = json.load(open(sys.argv[1])); B = json.load(open(sys.argv[2])); rv = int(sys.argv[3]) if len(sys.argv) > 3 else 1
G = N["gates"]; names = N["nodes"]; idx = {n: i for i, n in enumerate(names)}
bb = B["boundary"]; env = set(idx[x] for x in B["env"])
X = 2
val = [X] * len(names)
val[idx[bb["rst"]]] = rv
readers = collections.defaultdict(list)
drv = {}
for gi, g in enumerate(G):
    if g["out"] in env: continue            # circuit N B: gates driving environment nodes removed
    drv[g["out"]] = gi
    for i in set(g["ins"]): readers[i].append(gi)
def ev(g):
    ins = [val[i] for i in g["ins"]]
    xs = [k for k, v in enumerate(ins) if v == X]
    base = sum((v & 1) << k for k, v in enumerate(ins) if v != X)
    outs = set()
    for bits in itertools.product((0, 1), repeat=len(xs)):
        a = base + sum(b << k for b, k in zip(bits, xs))
        outs.add((g["init"] >> a) & 1)
        if len(outs) > 1: return X
    return outs.pop()
work = collections.deque(range(len(G)))
inq = [True] * len(G); steps = 0
while work:
    gi = work.popleft(); inq[gi] = False; g = G[gi]
    if g["out"] in env: continue
    v = ev(g); steps += 1
    if v != val[g["out"]]:
        assert val[g["out"]] == X, "non-monotone"   # Kleene from X only ever refines X
        val[g["out"]] = v
        for r in readers[g["out"]]:
            if not inq[r]: inq[r] = True; work.append(r)
show = lambda v: {0: "0", 1: "1", X: "X"}[v]
print("rst =", rv, "; evaluations", steps)
for k in ("a_ack", "b_ack", "start_ack", "out0_req", "pend_ack", "out0_ack", "req"):
    print("  %-9s %-18s %s" % (k, bb[k], show(val[idx[bb[k]]])))
d = collections.Counter(show(val[g["out"]]) for g in G if g["out"] not in env and not (g["k"] == 1 and g["init"] == 2))
print("logic gate outputs:", dict(d))
