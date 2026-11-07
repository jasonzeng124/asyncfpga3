#!/usr/bin/env python3
"""Shard B (UNTRUSTED), 2026-11-07: controlling-SET hold certificate (Formal.Cells.CtlChain.hold_set/cert_holds) for
node B after cause A changes at tau, on a simb.py dump. Roots (premises): A shows its old value until tau-1, and every
node whose value does not change in [tau, nc(B)] in the run holds it until its next change ("static" premise; an
order-level fact the network argument must supply). For each changing node n, in run order, U(n) = the latest time
n is certified to keep its pre-tau value = max over controlling pin sets P (INIT = n's value whenever P's pins show
their pre-tau source values; tied pins constant) of min over j in P of U(src j) + dmin_j. Prints U(B) - tau + 1 (the
sound-shape lower bound on B's change after A, given the premises), and the number of static premises used.
Feedback pins are fixed at the node's own value (a memory hold, by induction; not yet in Lean).
usage: ctlcert.py NET.json DUMP.json A TAU B C KAPPA"""
import json, sys, math, itertools
N = json.load(open(sys.argv[1])); D = json.load(open(sys.argv[2]))["nodes"]
idx = {n: i for i, n in enumerate(N["nodes"])}
A = idx[sys.argv[3]]; TAU = int(sys.argv[4]); Bn = idx[sys.argv[5]]; C = float(sys.argv[6]); K = float(sys.argv[7])
gates = N["gates"]; drv = {g["out"]: gi for gi, g in enumerate(gates)}
RST = idx.get("SLICE_X2Y29.DQ")
def root(n):
    m, s = n, 0
    while m in drv and gates[drv[m]]["k"] == 1 and gates[drv[m]]["init"] == 2 and s < 300: m = gates[drv[m]]["ins"][0]; s += 1
    return m
def isconst(n): r = root(n); return (r in drv and gates[drv[r]]["k"] == 0) or r == RST
def cval(n): r = root(n); return False if r == RST else bool(gates[drv[r]]["init"] & 1)
def val(n, t):
    d = D.get(str(n))
    if d is None: return cval(n) if isconst(n) else None
    v = d[0]
    for s in d[1]:
        if s <= t: v = not v
        else: break
    return v
def nc(n):
    d = D.get(str(n))
    if d is None: return None
    for s in d[1]:
        if s >= TAU: return s
    return None
def dmin(e): return math.ceil((1 - K) * ((1 - C) * e["fmin"] + C * e["smin"]) - 1e-9)
t0 = TAU - 1; tB = nc(Bn); INF = 10 ** 15
U = {}
def Uof(m):
    if m == A: return t0
    if m in U: return U[m]
    x = nc(m)
    if x is None or x > tB: return (x - 1) if x is not None else INF   # static premise
    return None
changing = sorted((nc(int(k)), int(k)) for k in D if nc(int(k)) is not None and nc(int(k)) <= tB and int(k) != A)
static_used = set(); WHY = {}
for _pass in range(60):
  nU = len(U)
  for tn, n in changing:
    if n not in drv or n in U: continue
    g = gates[drv[n]]; k, I = g["k"], g["init"]; w = val(n, t0)
    fbp = [j for j in range(k) if root(g["ins"][j]) == n]
    pins = [j for j in range(k) if not isconst(g["ins"][j]) and j not in fbp]
    fix = {j: cval(g["ins"][j]) for j in range(k) if isconst(g["ins"][j])}
    for j in fbp: fix[j] = w   # memory hold: the node's own feedback shows w (inductive; CtlChain needs hold_mem)
    best = None; bestP = None
    for r in range(1, len(pins) + 1):
        for P in itertools.combinations(pins, r):
            f = dict(fix)
            for j in P: f[j] = val(g["ins"][j], t0)
            if any(v is None for v in f.values()): continue
            if not all(((I >> a) & 1) == w for a in range(1 << k) if all(((a >> i) & 1) == v for i, v in f.items())): continue
            us = [Uof(g["ins"][j]) for j in P]
            if any(u is None for u in us): continue
            u = min(uu + dmin(g["arcs"][j]) for uu, j in zip(us, P))
            if best is None or u > best: best, bestP = u, P
    if best is not None:
        U[n] = best; WHY[n] = bestP
        for j in bestP:
            m = g["ins"][j]
            if m != A and m not in U: static_used.add(root(m))
  if len(U) == nU: break
print("changing nodes in [tau, nc(B)]:", len(changing), " certified:", len(U))
if Bn in U: print("U(B) - tau + 1 =", U[Bn] - t0, " (actual B change - tau =", tB - TAU, ")  static premises used:", len(static_used))
else: print("B not certified")

if Bn in U and "--tree" in sys.argv:
    # the dependency tree of B's certificate at LUT level (copies collapsed), with the static premises it uses
    seen = set(); out = []
    def walk(n, d):
        if n == A: out.append("  " * d + "CAUSE " + N["nodes"][n]); return
        if n not in U:
            out.append("  " * d + "STATIC %s = %s until %s" % (N["nodes"][n], val(n, t0), Uof(n))); return
        g = gates[drv[n]]
        if g["k"] == 1 and g["init"] == 2: return walk(g["ins"][0], d)
        out.append("  " * d + "%s (w=%s) U-t0=%d via pins %s" % (g["name"], val(n, t0), U[n] - t0, list(WHY[n])))
        if n in seen: return
        seen.add(n)
        for j in WHY[n]: walk(g["ins"][j], d + 1)
    walk(Bn, 0)
    print("\n".join(out)); print("LUT steps:", len(seen))
if Bn in U and "--chainjson" in sys.argv:
    # the certificate as a single chain from the target back to the cause, if every step has exactly one pin whose
    # source is certified (not static) -- RaceTablePS-style path [(gate, pin) ...] from the target side to the cause
    out = []; n = Bn; ok = True
    while n != A:
        if n not in U: ok = False; break
        g = gates[drv[n]]
        if g["k"] == 1 and g["init"] == 2: n = g["ins"][0]; continue
        dyn = [j for j in WHY[n] if root(g["ins"][j]) == A or root(g["ins"][j]) in U]
        if len(dyn) != 1: ok = False; break
        out.append((drv[n], dyn[0])); n = root(g["ins"][dyn[0]])
    path = sys.argv[sys.argv.index("--chainjson") + 1]
    json.dump(dict(ok=ok, path=out), open(path, "w")); print("chain", ok, len(out))
