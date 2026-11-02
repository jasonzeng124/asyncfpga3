#!/usr/bin/env python3
"""island_own.py (audit T15): the self-confirming idle island of THE target, from the auditor's own decode.
1. Reset state: 3-valued fixpoint with rst = 1, the shared request = 0, out0_ack = 0, pend_ack = 0 (n = 0: the env never
   requests, so it never acknowledges), data and everything else X (as reset_x.py).
2. Island = greatest set S of definite nodes such that, with rst = 0, request/acks 0, every member's gate output is
   FORCED to its value by the values of members alone (non-members X). Iterate: drop any member not forced.
Prints |S| and whether the four boundary handshake outputs are in S at 0.   python3 -I island_own.py NET.json BND.json"""
import json, sys, collections, itertools
N = json.load(open(sys.argv[1])); B = json.load(open(sys.argv[2]))
G = N["gates"]; names = N["nodes"]; idx = {n: i for i, n in enumerate(names)}
bb = B["boundary"]; env = set(idx[x] for x in B["env"]); X = 2
gates = [g for g in G if g["out"] not in env]
readers = collections.defaultdict(list)
for gi, g in enumerate(gates):
    for i in set(g["ins"]): readers[i].append(gi)
def ev(g, val):
    ins = [val[i] for i in g["ins"]]; xs = [k for k, v in enumerate(ins) if v == X]
    base = sum((v & 1) << k for k, v in enumerate(ins) if v != X); outs = set()
    for bits in itertools.product((0, 1), repeat=len(xs)):
        outs.add((g["init"] >> (base + sum(b << k for b, k in zip(bits, xs)))) & 1)
        if len(outs) > 1: return X
    return outs.pop()
def fix(val):
    work = collections.deque(range(len(gates))); inq = [True] * len(gates)
    while work:
        gi = work.popleft(); inq[gi] = False; g = gates[gi]; v = ev(g, val)
        if v != val[g["out"]]:
            val[g["out"]] = v
            for r in readers[g["out"]]:
                if not inq[r]: inq[r] = True; work.append(r)
    return val
envfix = {idx[bb["req"]]: 0, idx[bb["out0_ack"]]: 0, idx[bb["pend_ack"]]: 0}
val = [X] * len(names); val[idx[bb["rst"]]] = 1
for n, v in envfix.items(): val[n] = v
val = fix(val)
outs = ("a_ack", "b_ack", "start_ack", "out0_req")
print("reset state:", {k: val[idx[bb[k]]] for k in outs}, "definite gate outputs:", sum(val[g["out"]] != X for g in gates))
# greatest self-confirming set under rst = 0
mem = {g["out"]: val[g["out"]] for g in gates if val[g["out"]] != X}
fixed = dict(envfix); fixed[idx[bb["rst"]]] = 0
drvg = {g["out"]: g for g in gates}
changed = True; rounds = 0
while changed:
    changed = False; rounds += 1
    cur = [X] * len(names)
    for n, v in fixed.items(): cur[n] = v
    for n, v in mem.items(): cur[n] = v
    for n in list(mem):
        if ev(drvg[n], cur) != mem[n]:
            del mem[n]; changed = True
copy = lambda g: g["k"] == 1 and g["init"] == 2
logic_mem = [n for n in mem if not copy(drvg[n])]
print("island: %d nodes (%d logic gate outputs) after %d rounds" % (len(mem), len(logic_mem), rounds))
print("boundary outputs in island:", {k: mem.get(idx[bb[k]], "OUT") for k in outs})
