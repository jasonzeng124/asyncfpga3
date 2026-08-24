#!/usr/bin/env python3
"""Fit gcd's per-run cost from its four replayed loop counters.

  cycles/run = base + k1*k_loop + k2*pre_ctz + k3*main + k4*inner_ctz

Unlike isprime's, these four are not linearly dependent -- shared powers of two
move only k_loop, a one-sided even operand moves only pre_ctz, and an odd
coprime pair moves only main and inner_ctz -- but main and inner_ctz ARE
correlated (each main iteration usually shifts at least once), so the standard
errors are what decides whether the split between them is real.
"""
import sys, math

rows = []
path = sys.argv[1] if len(sys.argv) > 1 else "build/hw/gcd_cost.tsv"
with open(path) as f:
    next(f)
    for ln in f:
        a, b, k, cp, mn, ci, res, cyc, lo, hi = ln.split()
        rows.append((a, b, int(k), int(cp), int(mn), int(ci), float(cyc) / 200.0))

names = ["base (entry + exit + harness)", "per k loop iteration ((a|b)&1)==0",
         "per pre-loop ctz shift", "per MAIN loop iteration",
         "per inner ctz shift"]
X = [[1.0, float(k), float(cp), float(mn), float(ci)] for _, _, k, cp, mn, ci, _ in rows]
y = [c for *_, c in rows]
n = len(names)
XtX = [[sum(X[i][a] * X[i][b] for i in range(len(X))) for b in range(n)] for a in range(n)]
Xty = [sum(X[i][a] * y[i] for i in range(len(X))) for a in range(n)]
M = [XtX[r][:] + [1.0 if c == r else 0.0 for c in range(n)] + [Xty[r]] for r in range(n)]
for c in range(n):
    p = max(range(c, n), key=lambda r: abs(M[r][c]))
    M[c], M[p] = M[p], M[c]
    d = M[c][c]
    M[c] = [v / d for v in M[c]]
    for r in range(n):
        if r != c and M[r][c]:
            f = M[r][c]
            M[r] = [v - f * w for v, w in zip(M[r], M[c])]
beta = [M[r][2 * n] for r in range(n)]
inv = [[M[r][n + c] for c in range(n)] for r in range(n)]
resid = [y[i] - sum(beta[a] * X[i][a] for a in range(n)) for i in range(len(X))]
dof = len(X) - n
s2 = sum(r * r for r in resid) / dof

print()
for a in range(n):
    se = math.sqrt(s2 * inv[a][a])
    flag = "   <-- not resolved" if abs(beta[a]) < 2 * se else ""
    print(f"  {names[a]:<36} {beta[a]:>8.3f} +- {se:.3f} cycles   ({beta[a]*10:>7.1f} ns){flag}")
print(f"  residual RMS {math.sqrt(s2):.3f} cycles over {len(X)} points, {dof} dof")
print()
print("            a            b    k  pre  main  ctz   measured    resid")
for (a, b, k, cp, mn, ci, c), r in zip(rows, resid):
    print(f"  {a:>11} {b:>12} {k:>4} {cp:>4} {mn:>5} {ci:>4}  {c:>9.2f}  {r:>+7.2f}")
