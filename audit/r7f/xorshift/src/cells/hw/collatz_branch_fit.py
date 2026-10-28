#!/usr/bin/env python3
"""Fit cycles/run = base + a*even_steps + b*odd_steps, with standard errors.

Ordinary least squares by hand (no numpy dependency in this tree).  The
standard errors matter more than the point estimates: the two step counts are
correlated across natural collatz trajectories, and the only reason b is
identifiable at all is the powers-of-two rows where odd == 0.
"""
import sys, math

rows = []
path = sys.argv[1] if len(sys.argv) > 1 else "build/hw/collatz_branch_collatz.tsv"
with open(path) as f:
    next(f)
    for ln in f:
        n, ev, od, st, cyc, lo, hi = ln.split()
        rows.append((int(ev), int(od), float(cyc) / 200.0))

X = [[1.0, float(e), float(o)] for e, o, _ in rows]
y = [c for _, _, c in rows]
k = 3
XtX = [[sum(X[i][a] * X[i][b] for i in range(len(X))) for b in range(k)] for a in range(k)]
Xty = [sum(X[i][a] * y[i] for i in range(len(X))) for a in range(k)]

# Gauss-Jordan on [XtX | I] to get both the solution and the covariance factor
M = [XtX[r][:] + [1.0 if c == r else 0.0 for c in range(k)] + [Xty[r]] for r in range(k)]
for c in range(k):
    p = max(range(c, k), key=lambda r: abs(M[r][c]))
    M[c], M[p] = M[p], M[c]
    d = M[c][c]
    M[c] = [v / d for v in M[c]]
    for r in range(k):
        if r != c and M[r][c]:
            f = M[r][c]
            M[r] = [v - f * w for v, w in zip(M[r], M[c])]
beta = [M[r][2 * k] for r in range(k)]
inv = [[M[r][k + c] for c in range(k)] for r in range(k)]

resid = [y[i] - sum(beta[a] * X[i][a] for a in range(k)) for i in range(len(X))]
dof = len(X) - k
s2 = sum(r * r for r in resid) / dof
se = [math.sqrt(s2 * inv[a][a]) for a in range(k)]
names = ["base (entry+exit+harness)", "per EVEN step (n>>1)", "per ODD step (3n+1)"]

print()
for a in range(k):
    print(f"  {names[a]:<28} {beta[a]:>8.3f} +- {se[a]:.3f} cycles"
          f"   ({beta[a]*10:>7.1f} +- {se[a]*10:.1f} ns at 100 MHz)")
print(f"  residual RMS {math.sqrt(s2):.3f} cycles over {len(X)} points, {dof} dof")
print(f"  odd/even cost ratio {beta[2]/beta[1]:.2f}")
print()
print("  n      even odd  measured  fitted   resid")
for (e, o, c), r in zip(rows, resid):
    print(f"  {'':<6} {e:>4} {o:>3}  {c:>8.2f} {c-r:>7.2f} {r:>+7.2f}")
