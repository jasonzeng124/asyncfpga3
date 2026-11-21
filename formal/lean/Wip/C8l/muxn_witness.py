#!/usr/bin/env python3
"""Unit-delay run of the bdc_muxn3 model (OpsMuxNOp.MuxN) for the non-vacuity witness:
the control channel offers select 1, input 1 offers one token, z's receiver acks one tick
after the request.  Prints the trace tables (Lean list syntax).  Proves nothing."""
S = 1
names = ["r0", "r1", "r2", "a0", "a1", "a2", "cr", "ca", "zr", "za", "j0", "j1", "j2"]
st = {n: 0 for n in names}
rows = [dict(st)]
def C(a, b, q): return (a & b) | (q & (a | b))
for t in range(40):
    c = rows[-1]; n = dict(c)
    # environment: input 1 and control send one token each, starting at t = 0
    for (r, a) in [("r1", "a1"), ("cr", "ca")]:
        if c[r] == c[a]:
            n[r] = 1 if (c[r] == 0 and t == 0) else 0 if c[r] == 1 else c[r]
    n["za"] = c["zr"]
    for k in range(3):
        n[f"j{k}"] = C(c[f"r{k}"], int(c["cr"] and S == k), c[f"j{k}"])
        n[f"a{k}"] = C(c[f"j{k}"], c["za"], c[f"a{k}"])
    n["zr"] = int(c["j0"] or c["j1"] or c["j2"])
    n["ca"] = c["za"]
    rows.append(n)
    if n == c and t > 2: break
T = len(rows)
print("-- steps", T)
for nm in names:
    print(f"def w_{nm} : Trace := tr [" + ", ".join("true" if r[nm] else "false" for r in rows) + "]")
