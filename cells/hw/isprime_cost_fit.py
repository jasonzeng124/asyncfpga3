#!/usr/bin/env python3
"""Fit isprime's per-run cost from its replayed loop counts.

  cycles/run = base + a*outer_trials + b*inner_shift_steps + c*[early return]

(outer, inner) is a full-rank basis: the raw shift-up and shift-down counts are
linearly dependent (down == up + outer), so fitting all three would report a
decomposition the data cannot support.

The early-return indicator is not decoration.  Without it the fit leaves
structured residuals -- composites all low, primes all high, the two
loop-skipping inputs +9 -- because isprime's exit block is reached from three
different places and the r==0 return does strictly less work in its last trial
than falling out of the d*d<=n test does.  Adding one indicator column drops
the residual RMS from 4.46 to 1.41 cycles.
"""
import sys, math

rows = []
path = sys.argv[1] if len(sys.argv) > 1 else "build/hw/isprime_cost.tsv"
with open(path) as f:
    next(f)
    for ln in f:
        n, o, i, res, cyc, lo, hi = ln.split()
        rows.append((int(n), int(o), int(i), int(res), float(cyc) / 200.0))

names = ["base (entry + exit + harness)", "per OUTER trial (d*d<=n, r==0, d+1)",
         "per INNER shift step", "early-return saving (composite)"]
X = [[1.0, float(o), float(i), 0.0 if res else 1.0] for _, o, i, res, _ in rows]
y = [c for *_, c in rows]
k = len(names)
XtX = [[sum(X[i][a] * X[i][b] for i in range(len(X))) for b in range(k)] for a in range(k)]
Xty = [sum(X[i][a] * y[i] for i in range(len(X))) for a in range(k)]
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

print()
for a in range(k):
    se = math.sqrt(s2 * inv[a][a])
    print(f"  {names[a]:<38} {beta[a]:>9.3f} +- {se:.3f} cycles   ({beta[a]*10:>8.1f} ns at 100 MHz)")
print(f"  residual RMS {math.sqrt(s2):.3f} cycles over {len(X)} points, {dof} dof")
print()
print("       n  outer  inner  prime   measured    resid")
for (n, o, i, res, c), r in zip(rows, resid):
    print(f"  {n:>6} {o:>6} {i:>6} {res:>6}  {c:>9.2f}  {r:>+7.2f}")
