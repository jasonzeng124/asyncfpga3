#!/usr/bin/env python3
"""Explicit-state reachability of bdc_muxn (N = 3) in the same SI model as 8f's
bd_mux (OpsMux): j_k = C(in_k_req, ctl_req . (s == k)), z_req = delta(OR j),
in_k_ack = C(j_k, z_ack), ctl_ack = DI wire of z_ack, s held by the ctl
channel's bundling. Counters: dc = #ctl^ - #z^, d_k = 1 + #in_k^ - #ctl^(s=k).
Reports the reachable-set size (feasibility of the OpsMux method). Proves nothing."""
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 3
sig = [f"r{k}" for k in range(N)] + [f"a{k}" for k in range(N)] + ["cr", "ca", "zr", "za"] + [f"j{k}" for k in range(N)]
W = len(sig)
B = [{n: (v >> i) & 1 for i, n in enumerate(sig)} for v in range(1 << W)]
def succs(v, s):
    c = B[v]
    # enumerate next values gate by gate (each may hold or move to its allowed value)
    opts = []
    for k in range(N):
        opts.append((f"r{k}", [c[f"r{k}"]] + ([1 - c[f"r{k}"]] if c[f"r{k}"] == c[f"a{k}"] else [])))
    opts.append(("cr", [c["cr"]] + ([1 - c["cr"]] if c["cr"] == c["ca"] else [])))
    opts.append(("za", [c["za"]] + ([1 - c["za"]] if c["za"] != c["zr"] else [])))
    for k in range(N):
        tgt = c[f"r{k}"]; ok = tgt == (c["cr"] and s == k)
        opts.append((f"j{k}", [c[f"j{k}"]] + ([tgt] if ok and tgt != c[f"j{k}"] else [])))
    orj = int(any(c[f"j{k}"] for k in range(N)))
    opts.append(("zr", [c["zr"]] + ([orj] if orj != c["zr"] else [])))
    for k in range(N):
        ok = c[f"j{k}"] == c["za"]
        opts.append((f"a{k}", [c[f"a{k}"]] + ([c["za"]] if ok and c["za"] != c[f"a{k}"] else [])))
    opts.append(("ca", [c["ca"]] + ([c["za"]] if c["za"] != c["ca"] else [])))
    res = [{}]
    for n, vals in opts:
        res = [dict(d, **{n: x}) for d in res for x in vals]
    for d in res:
        v2 = sum(d[n] << i for i, n in enumerate(sig))
        idle = not (c["cr"] or c["ca"]) or not (d["cr"] or d["ca"])
        for s2 in (range(N) if idle else [s]):
            yield v2, s2, d, c
init = [(0, s, 0, (1,) * N) for s in range(N)]
seen = set(init); todo = list(init); bad = 0
while todo:
    v, s, dc, dk = todo.pop()
    for v2, s2, d, c in succs(v, s):
        rc = (not c["cr"]) and d["cr"]; rz = (not c["zr"]) and d["zr"]
        dk2 = tuple(dk[k] + ((not c[f"r{k}"]) and d[f"r{k}"]) - (rc and s2 == k) for k in range(N))
        st = (v2, s2, dc + rc - rz, dk2)
        if abs(st[2]) > 3 or any(abs(x) > 3 for x in dk2): print("diverge"); sys.exit(1)
        if c["zr"] != d["zr"] and c["zr"] != c["za"]: bad += 1
        for k in range(N):
            if c[f"a{k}"] != d[f"a{k}"] and c[f"a{k}"] == c[f"r{k}"]: bad += 1
        if c["ca"] != d["ca"] and c["ca"] == c["cr"]: bad += 1
        if st not in seen: seen.add(st); todo.append(st)
print("N =", N, "reachable states:", len(seen), "protocol violations:", bad)
