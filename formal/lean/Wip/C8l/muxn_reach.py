#!/usr/bin/env python3
"""Reachable set of bdc_muxn N = 3 (bdc/emit.py emit_muxn) in the SI model of
Formal/Net/OpsMuxN.lean:
  j_k = C(in_k_req, ctl_req . (s == k))   (bd_c2, s = low 2 bits of ctl data)
  z_req = delta(OR j)                     (uor + matched delay, one inertial node)
  in_k_ack = C(j_k, z_ack)                (bd_c2)
  ctl_ack = z_ack                         (DI wire)
s ranges over 0..3 (3 selects nothing: the token waits forever; safe).
Counters: dc = #ctl^ - #z^, d_k = 1 + #in_k^ - #ctl^(s = k).
With -lean prints the Lean data (membership bitmask over the 15-bit state code
and a per-code counter byte).  Proves nothing; Lean re-checks the closure."""
import sys
N = 3
NS = 4
names = [f"r{k}" for k in range(N)] + [f"a{k}" for k in range(N)] + ["cr", "ca", "zr", "za"] + [f"j{k}" for k in range(N)]
def code(c, s):
    v = 0
    for i, n in enumerate(names):
        v |= int(c[n]) << i
    return v | (s << 13)
def succs(c, s):
    opts = []
    for k in range(N):
        opts.append((f"r{k}", [c[f"r{k}"]] + ([1 - c[f"r{k}"]] if c[f"r{k}"] == c[f"a{k}"] else [])))
    opts.append(("cr", [c["cr"]] + ([1 - c["cr"]] if c["cr"] == c["ca"] else [])))
    opts.append(("za", [c["za"]] + ([1 - c["za"]] if c["za"] != c["zr"] else [])))
    for k in range(N):
        tgt = c[f"r{k}"]; ok = tgt == int(c["cr"] and s == k)
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
        idle = not (c["cr"] or c["ca"]) or not (d["cr"] or d["ca"])
        for s2 in (range(NS) if idle else [s]):
            yield d, s2
z = {n: 0 for n in names}
init = [(tuple(sorted(z.items())), s, 0, (1,) * N) for s in range(NS)]
seen = set(init); todo = list(init); bad = 0; ntrans = 0
while todo:
    ct, s, dc, dk = todo.pop()
    c = dict(ct)
    for d, s2 in succs(c, s):
        ntrans += 1
        rc = int((not c["cr"]) and d["cr"]); rz = int((not c["zr"]) and d["zr"])
        dk2 = tuple(dk[k] + int((not c[f"r{k}"]) and d[f"r{k}"]) - int(rc and s2 == k) for k in range(N))
        dc2 = dc + rc - rz
        if dc2 < 0 or dc2 > 1 or any(x < 0 or x > 3 for x in dk2): print("diverge", file=sys.stderr); sys.exit(1)
        if c["zr"] != d["zr"] and c["zr"] != c["za"]: bad += 1
        for k in range(N):
            if c[f"a{k}"] != d[f"a{k}"] and c[f"a{k}"] == c[f"r{k}"]: bad += 1
        if c["ca"] != d["ca"] and c["ca"] == c["cr"]: bad += 1
        if rz:
            ok = c["cr"] and not c["ca"] and not c["za"] and dc == 1 and s < N and \
                c[f"r{s}"] and not c[f"a{s}"] and dk[s] == 1
            if not ok: bad += 1
        st = (tuple(sorted(d.items())), s2, dc2, dk2)
        if st not in seen: seen.add(st); todo.append(st)
fun = {}
for ct, s, dc, dk in seen:
    fun.setdefault(code(dict(ct), s), set()).add((dc,) + dk)
print("N =", N, "reachable states:", len(seen), "codes:", len(fun), "transitions:", ntrans,
      "protocol violations:", bad, "counters functional:", all(len(v) == 1 for v in fun.values()),
      "max d:", max(max(x) for v in fun.values() for x in v), file=sys.stderr)
if "-lean" in sys.argv:
    T = 0
    for cd, v in fun.items():
        (dc, d0, d1, d2), = v
        byte = 1 | (dc << 1) | (d0 << 2) | (d1 << 4) | (d2 << 6)
        T |= byte << (8 * cd)
    print("def TB : Nat := 0x%x" % T)
    print("def codes : List Nat := [" + ", ".join(str(x) for x in sorted(fun)) + "]")
