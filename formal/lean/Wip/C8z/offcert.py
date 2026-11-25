#!/usr/bin/env python3
"""C-8z: compute an offer-bound certificate for every channel of gcd_hw.

Bound form: offers(c) <= al*L + be (L = walk length, spine channels <= L).
Rules (each proved in Lean as a local lemma, CapstoneLiveNdOff):
  sp           : c is a spine channel                         -> (1, 0)
  up d         : producer fork/join/bjoin/steer/link, d its input  -> B(d)
  up2 d e      : producer amerge (x, y) or mux (x, y)         -> B(d) + B(e)
  up3 d e f    : producer muxn (x0, x1, x2)                   -> B(d) + B(e) + B(f)
  dn d k       : consumer fork (d an output), join/bjoin/mux/muxn/amerge (d = output) k=1,
                 link (d = output) k=2                         -> B(d) + k
  dn2 d e      : consumer steer (d = t, e = f)                 -> B(d) + B(e) + 1
Derivation is by rounds (acyclic): a channel gets a bound only from channels bounded in
earlier rounds.  Usage: python3 -I offcert.py [--lean]
"""
import os, sys, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ndsim import sim, spine  # noqa: E402

names, ops, out0 = sim.load_net()
NC = len(names)
sp = spine()
prod, cons = {}, {}
for n, o in enumerate(ops):
    for c in sim.outs_of(o): prod[c] = n
    for c in sim.ins_of(o): cons[c] = n


def cands(c):
    """(rule, deps, fn) candidates; fn maps dep bounds to a bound."""
    out = []
    if sp[c]: out.append((("sp",), [], lambda: (1, 0)))
    o = ops[prod[c]]; k = o["k"]
    if k in ("forkG", "forkH", "steerC", "steerD", "link"):
        d = o["i"] if k in ("forkG", "forkH", "link") else o["j"]
        out.append((("up", d), [d], None))
    elif k in ("join", "bjoin"):
        for d in o["ins"]: out.append((("up", d), [d], None))
    elif k in ("amerge", "mux"):
        out.append((("up2", o["x"], o["y"]), [o["x"], o["y"]], None))
    elif k == "muxn":
        out.append((("up3", *o["xs"]), list(o["xs"]), None))
    if c in cons:
        o = ops[cons[c]]; k = o["k"]
        if k in ("forkG", "forkH"):
            for d in o["os"]: out.append((("dn", d, 1), [d], None))
        elif k in ("join", "bjoin"): out.append((("dn", o["o"], 1), [o["o"]], None))
        elif k in ("mux", "muxn", "amerge"): out.append((("dn", o["z"], 1), [o["z"]], None))
        elif k == "link": out.append((("dn", o["o"], 2), [o["o"]], None))
        elif k in ("steerC", "steerD"):
            out.append((("dn2", o["t"], o["f"]), [o["t"], o["f"]], None))
    return out


def val(rule, B):
    r = rule[0]
    if r == "sp": return (1, 0)
    if r == "up": return B[rule[1]]
    if r == "up2":
        a, b = B[rule[1]], B[rule[2]]; return (a[0] + b[0], a[1] + b[1])
    if r == "up3":
        a, b, d = B[rule[1]], B[rule[2]], B[rule[3]]; return (a[0] + b[0] + d[0], a[1] + b[1] + d[1])
    if r == "dn":
        a = B[rule[1]]; return (a[0], a[1] + rule[2])
    if r == "dn2":
        a, b = B[rule[1]], B[rule[2]]; return (a[0] + b[0], a[1] + b[1] + 1)


B, R, ORD = {}, {}, {}
rnd = 0
while True:
    new = {}
    for c in range(NC):
        if c in B: continue
        best = None
        for rule, deps, _ in cands(c):
            if all(d in B for d in deps):
                v = val(rule, B)
                if best is None or v < best[0]: best = (v, rule)
        if best: new[c] = best
    if not new: break
    for c, (v, rule) in new.items():
        B[c] = v; R[c] = rule; ORD[c] = rnd
    rnd += 1

missing = [names[c] for c in range(NC) if c not in B]
print(f"rounds {rnd}, bounded {len(B)}/{NC}, unbounded: {missing[:20]}", file=sys.stderr)
if B:
    amax = max(v[0] for v in B.values()); bmax = max(v[1] for v in B.values())
    worst = max(B, key=lambda c: B[c])
    print(f"max al {amax}, max be {bmax}; worst {names[worst]} {B[worst]}", file=sys.stderr)
    ns = [c for c in B if not sp[c]]
    print(f"non-spine max al {max(B[c][0] for c in ns)}, max be {max(B[c][1] for c in ns)}", file=sys.stderr)

if "--lean" in sys.argv and not missing:
    def enc(rule):
        r = rule[0]
        if r == "sp": return ".sp"
        if r == "up": return f".up {rule[1]}"
        if r == "up2": return f".up2 {rule[1]} {rule[2]}"
        if r == "up3": return f".up3 {rule[1]} {rule[2]} {rule[3]}"
        if r == "dn": return f".dn {rule[1]} {rule[2]}"
        if r == "dn2": return f".dn2 {rule[1]} {rule[2]}"
    rows = [f"⟨{enc(R[c])}, {B[c][0]}, {B[c][1]}, {ORD[c]}⟩" for c in range(NC)]
    print("[" + ",\n  ".join(rows) + "]")
