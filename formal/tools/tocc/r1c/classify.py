#!/usr/bin/env python3
"""Shard C helper (UNTRUSTED): exact/data split of the collapsed cone. Imported by the other tools.
EXACT: control storage (storage nodes that are not latch-like), comb gates on a comb path from an exact
source (control storage / env handshake) to an exact sink (control storage, the kernel's handshake outputs,
a data latch's ENABLE pin), env handshake nodes. DATA: data latches, every other comb gate, operand buses."""
import pickle, collections, sys

def lut(init, k, bits):
    a = 0
    for j, b in enumerate(bits):
        if b: a |= 1 << j
    return (init >> a) & 1

def load(fn="/tmp/claude-0/r1c/model.pkl"):
    M = pickle.load(open(fn, "rb"))
    gates = M["gates"]; ENV = set(M["ENV"]); names = M["names"]; bs = M["bsrc"]
    const = {n for n, g in gates.items() if g["k"] == 0}
    live = {n: [p for p in g["pins"] if p["live"]] for n, g in gates.items()}
    stor = {n for n in gates if n not in const and any(p["src"] == n for p in live[n])}
    def latch_info(n):
        g = gates[n]; k, I = g["k"], g["init"]
        fb = [j for j, p in enumerate(g["pins"]) if p["src"] == n and p["live"]]
        fbj = fb[0]; en = []
        for p in range(k):
            pp = g["pins"][p]
            if p == fbj or not pp["live"] or pp["src"] in ENV: continue
            for v in (0, 1):
                if all(((I >> x) & 1) == ((I >> (x ^ (1 << fbj))) & 1) for x in range(1 << k) if ((x >> p) & 1) == v):
                    en.append((p, v))
        return fb, en
    LATCH = {}
    for n in stor:
        fb, en = latch_info(n)
        if en: LATCH[n] = (fb, en)
    CTRL = stor - set(LATCH)
    hs_env = {bs[k] for k in ("rst", "req", "out0_ack", "pend_ack")}
    data_env = set(bs["a_data"]) | set(bs["b_data"])
    comb = {n for n in gates if n not in stor and n not in const}
    # forward from exact sources through comb
    fwd = set(); todo = list(CTRL | hs_env)
    rd = collections.defaultdict(set)
    for n in gates:
        for p in live[n]: rd[p["src"]].add(n)
    seen = set(todo)
    while todo:
        u = todo.pop()
        for v in rd[u]:
            if v in comb and v not in seen:
                seen.add(v); fwd.add(v); todo.append(v)
    # backward from exact sinks
    sinks = set()
    for n in CTRL:
        for p in live[n]: sinks.add(p["src"])
    for k in ("a_ack", "b_ack", "start_ack", "out0_req"): sinks.add(bs[k])
    for n, (fb, en) in LATCH.items():
        for p, v in en: sinks.add(gates[n]["pins"][p]["src"])
    bwd = set(); todo = [s for s in sinks if s in comb]; seen = set(todo); bwd |= seen
    while todo:
        u = todo.pop()
        for p in live[u]:
            s = p["src"]
            if s in comb and s not in seen:
                seen.add(s); bwd.add(s); todo.append(s)
    EXC = fwd & bwd
    EXACT = CTRL | EXC | hs_env
    DATA = set(LATCH) | (comb - EXC) | data_env
    return dict(M=M, gates=gates, live=live, names=names, ENV=ENV, const=const, stor=stor, LATCH=LATCH,
                CTRL=CTRL, EXC=EXC, EXACT=EXACT, DATA=DATA, hs_env=hs_env, data_env=data_env, bs=bs, rd=rd,
                comb=comb)

if __name__ == "__main__":
    C = load()
    g = C["gates"]
    print("logic gates %d, const %d, storage %d (latch-like %d, control %d), comb %d" % (
        len(g), len(C["const"]), len(C["stor"]), len(C["LATCH"]), len(C["CTRL"]), len(C["comb"])))
    print("exact comb %d, data comb %d" % (len(C["EXC"]), len(C["comb"]) - len(C["EXC"])))
    print("EXACT %d (ctrl stor %d + comb %d + env hs %d); DATA %d (latches %d + comb %d + env data %d)" % (
        len(C["EXACT"]), len(C["CTRL"]), len(C["EXC"]), len(C["hs_env"]), len(C["DATA"]), len(C["LATCH"]),
        len(C["comb"]) - len(C["EXC"]), len(C["data_env"])))
    # data nodes read by exact gates
    rdx = collections.Counter()
    for n in C["EXACT"]:
        if n not in g: continue
        for p in C["live"][n]:
            if p["src"] in C["DATA"]: rdx[p["src"]] += 1
    kinds = collections.Counter("latch" if s in C["LATCH"] else ("env" if s in C["data_env"] else "comb") for s in rdx)
    print("data nodes read by exact gates: %d %s; pins %d" % (len(rdx), dict(kinds), sum(rdx.values())))
    # exact nodes read by data gates (other than latch enables)
    en_src = collections.Counter()
    for n, (fb, en) in C["LATCH"].items():
        en_src[len(en)] += 1
    print("latch enable-pin counts", en_src)
    # exact gates read by data comb
    x = sum(1 for n in C["DATA"] if n in g for p in C["live"][n] if p["src"] in C["EXACT"])
    print("data-gate pins from exact nodes:", x)
    print("other env nodes:", [C["names"][e] for e in C["ENV"] if e not in C["hs_env"] and e not in C["data_env"]][:10])
