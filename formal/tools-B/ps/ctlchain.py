#!/usr/bin/env python3
"""Shard B (UNTRUSTED), 2026-11-07: sound-shape LOWER bound on when node B can change after cause node A changes at
tau (Formal.Cells.CtlChain): longest path from A over CONTROLLING pins, evaluated on the state of a simb.py dump just
before tau. A pin j of gate g controls g's output value w if INIT gives w at every address with pin j at its source's
pre-tau value and tied (constant-gate) pins at their constants ("plain"); with --mem also if that holds once the
feedback pin (source chain back to g's own output) is fixed at w ("memory": C-element hold, needs the node at w
before). LO(A) = tau - 1 (A shows its old value until then); LO(n) = max over controlling pins of LO(src) + dmin.
Prints LO(B) - (tau - 1) and the chain (gates, pins, values).  dmin = ceil((1-kappa)*lerp(fmin,smin,c)/g).
Tied pins: sources (through copy chains) that are constant gates, or the reset node (low from R on, an Env fact).
usage: ctlchain.py NET.json DUMP.json A_NAME TAU B_NAME C KAPPA [--mem]"""
import json, sys, math
N = json.load(open(sys.argv[1])); D = json.load(open(sys.argv[2]))["nodes"]
idx = {n: i for i, n in enumerate(N["nodes"])}
A = idx[sys.argv[3]]; TAU = int(sys.argv[4]); Bn = idx[sys.argv[5]]; C = float(sys.argv[6]); K = float(sys.argv[7])
MEM = "--mem" in sys.argv
gates = N["gates"]; drv = {g["out"]: gi for gi, g in enumerate(gates)}
def val(n, t):
    d = D.get(str(n))
    if d is None: return None if n not in drv or gates[drv[n]]["k"] else bool(gates[drv[n]]["init"] & 1)
    v = d[0]
    for s in d[1]:
        if s <= t: v = not v
        else: break
    return v
def dmin(e): return math.ceil((1 - K) * ((1 - C) * e["fmin"] + C * e["smin"]) - 1e-9)
RST = idx.get("SLICE_X2Y29.DQ")   # the reset node: low from R on (Env), treated as tied low
def root(n):
    m, seen = n, 0
    while m in drv and gates[drv[m]]["k"] == 1 and gates[drv[m]]["init"] == 2 and seen < 200:
        m = gates[drv[m]]["ins"][0]; seen += 1
    return m
def isconst(n):
    r = root(n); return (r in drv and gates[drv[r]]["k"] == 0) or r == RST
def cval(n):
    r = root(n); return False if r == RST else bool(gates[drv[r]]["init"] & 1)
def fbsrc(g, n):
    m = n; seen = 0
    while m in drv and gates[drv[m]]["k"] == 1 and gates[drv[m]]["init"] == 2 and seen < 200:
        if m == g["out"]: return True
        m = gates[drv[m]]["ins"][0]; seen += 1
    return m == g["out"]
def controls(g, j, t):
    k, I = g["k"], g["init"]; w = val(g["out"], t); b = val(g["ins"][j], t)
    if w is None or b is None: return False
    fix = {j: b}
    for i, n in enumerate(g["ins"]):
        if i != j and isconst(n): fix[i] = cval(n)
    fb = [i for i, n in enumerate(g["ins"]) if i != j and fbsrc(g, n)]
    for mode in (["plain", "mem"] if MEM else ["plain"]):
        f = dict(fix)
        if mode == "mem":
            if not fb: continue
            for i in fb: f[i] = w
        if all(((I >> a) & 1) == w for a in range(1 << k) if all(((a >> i) & 1) == v for i, v in f.items())):
            return mode
    return False
t0 = TAU - 1
def dmax(e): return math.floor((1 + K) * ((1 - C) * e["fmax"] + C * e["smax"]) + 1e-9)
def nc(n):
    d = D.get(str(n))
    if d is None: return None
    for s_ in d[1]:
        if s_ >= TAU: return s_
    return None
# time-respecting DAG: an edge m -> n only if m's first change at/after tau precedes n's (both change)
fan = {}
for gi, g in enumerate(gates):
    for j, n in enumerate(g["ins"]): fan.setdefault(n, []).append((gi, j))
order = sorted((nc(int(k)), int(k)) for k in D if nc(int(k)) is not None)
LO = {A: t0}; HI = {A: 0}; how = {}
for _pass in range(6):
 for tn, m in order:
    if m not in LO: continue
    for gi, j in fan.get(m, []):
        g = gates[gi]; n = g["out"]
        if n == A or nc(n) is None or nc(n) < tn: continue
        md = controls(g, j, t0)
        if not md: continue
        v = LO[m] + dmin(g["arcs"][j])
        if v > LO.get(n, -1):
            LO[n] = v; HI[n] = HI[m] + dmax(g["arcs"][j]); how[n] = (m, gi, j, md)
it = 0
print("nodes bounded", len(LO))
if Bn in LO:
    print("LO(B) - tau + 1 =", LO[Bn] - t0, " chain sum of upper delays =", HI[Bn], " actual B change - tau =", nc(Bn) - TAU)
    n, ch = Bn, []
    while n != A and len(ch) < 500:
        m, gi, j, md = how[n]; ch.append((gates[gi]["name"], j, md, LO[n] - t0)); n = m
    ch = list(reversed(ch)); luts = [c for c in ch if "LUT" in c[0]]
    print("  steps", len(ch), "LUT steps", len(luts), "mem steps", sum(1 for c in ch if c[2] == "mem"))
    for c in luts: print("  ", c)
else:
    print("B not reached by a controlling chain from A")
