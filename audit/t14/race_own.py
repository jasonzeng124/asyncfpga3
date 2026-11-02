#!/usr/bin/env python3
"""race_own.py (audit T14): a B race file (racePath/raceLoop arc lists, Lean) checked against the auditor's own decode.
    python3 -I race_own.py NET.json RACE.lean GATE_NAME PATH_PIN LOOP_PIN KAPPA...
(1) loop: from GATE's LOOP_PIN walk back through 1-input gates to GATE; arcs (B's order: back from the pin, then the
gate's own pin arc) must equal raceLoop. (2) path: chains of len(racePath)-1 (gate, pin) arcs from GATE's PATH_PIN back
to GATE's output whose arcs equal racePath[0..] in order (B's order: from the pin's driver back); the last arc is GATE's
own PATH_PIN arc. (3) sums at g = 1, c = 1/2 with the CURRENT Spec.Adm (owner decision 3):
lo = ceil((1-k) lerp(fmin,smin,c)/g), hi = floor((1+k) lerp(fmax,smax,c) g)."""
import json, math, re, sys
from fractions import Fraction as Fr
netp, leanp, gname, ppin, lpin = sys.argv[1:6]; ppin, lpin = int(ppin), int(lpin)
ks = [Fr(x) for x in sys.argv[6:]]
src = open(leanp).read()
def arcs(name):
    body = re.search(r"def %s : List Arc := \[(.*?)\]\n" % name, src, re.S).group(1)
    return [tuple(map(int, t)) for t in re.findall(r"⟨(\d+), (\d+), (\d+), (\d+)⟩", body)]
PATH, LOOP = arcs("racePath"), arcs("raceLoop")
N = json.load(open(netp)); G = N["gates"]
byout = {g["out"]: g for g in G}
A = lambda g, p: tuple(g["arcs"][p][k] for k in ("fmin", "fmax", "smin", "smax"))
X = next(g for g in G if g["name"] == gname)
loop = []; n = X["ins"][lpin]
while True:
    g = byout[n]
    if g is X: break
    assert g["k"] == 1, g["name"]
    loop.append(A(g, 0)); n = g["ins"][0]
loop.append(A(X, lpin))
print("loop: %d arcs, equal to raceLoop: %s" % (len(loop), loop == LOOP))
sols = []
def dfs(node, i, acc):
    if i == len(PATH) - 1:
        if node == X["out"]: sols.append(list(reversed(acc)))
        return
    g = byout.get(node)
    if g is None: return
    for p in range(g["k"]):
        if A(g, p) == PATH[i]:
            dfs(g["ins"][p], i + 1, acc + [(g["name"], p)])
print("path: last arc = gate pin %d arc: %s" % (ppin, A(X, ppin) == PATH[-1]))
dfs(X["ins"][ppin], 0, [(X["name"], ppin)])
print("path: %d matching chains of %d arcs from the gate's output to its pin %d" % (len(sols), len(PATH), ppin))
for s in sols[:2]:
    print("   ", " -> ".join(n for n, _ in s if not n.startswith(("hop", "~")) and ".O6" in n))
lo = lambda e, k: math.ceil((1 - k) * ((e[0] + e[2]) / Fr(2)))
hi = lambda e, k: math.floor((1 + k) * ((e[1] + e[3]) / Fr(2)))
for k in ks:
    pl = sum(lo(e, k) for e in PATH); lh = sum(hi(e, k) for e in LOOP)
    print("kappa %s: pathLo %d loopHi %d -> %s" % (float(k), pl, lh, "holds" if lh <= pl else "FAILS"))
