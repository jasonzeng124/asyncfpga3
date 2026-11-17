#!/usr/bin/env python3
"""isprime_fit.py RUN_LOG [FCLK_NS] -- isprime's per-loop cost from a ps7_bench.v run (one FIXED batch per n).
Model = cells/hw/isprime_cost_fit.py's: latency_ns = base + a*outer_trials + b*inner_shift_steps + c*[composite return],
with (outer, inner = shift-up + shift-down steps, result) counted from kernels/isprime/isprime.c's algorithm (the same
Python replay as cells/hw/isprime_cost.sh). latmin is in host clock cycles (FCLK_NS, default 12: fullstack_dump.sh
runs +FCLK_PS=12000). Batches that did not complete, disagree with the replayed result, or whose runs disagree are
left out."""
import re, sys


def counts(n):
    outer = up = down = 0; res = 1
    if n < 2:
        return 0, 0, 0
    d = 2
    while d * d <= n:
        outer += 1
        r = n; s = d; half = n >> 1
        while s <= half:
            s <<= 1; up += 1
        while s >= d:
            if r >= s:
                r -= s
            s >>= 1; down += 1
        if r == 0:
            res = 0; break
        d += 1
    return outer, up + down, res


def lstsq(X, y):
    n = len(X[0])
    A = [[sum(r[i] * r[j] for r in X) for j in range(n)] + [sum(r[i] * v for r, v in zip(X, y))] for i in range(n)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(A[r][c])); A[c], A[p] = A[p], A[c]
        for r in range(n):
            if r != c and A[c][c]:
                f = A[r][c] / A[c][c]; A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    beta = [A[i][n] / A[i][i] for i in range(n)]
    res = [v - sum(b * x for b, x in zip(beta, r)) for r, v in zip(X, y)]
    return beta, (sum(e * e for e in res) / max(1, len(X) - n)) ** 0.5


fclk = float(sys.argv[2]) if len(sys.argv) > 2 else 12.0
X, y, bad = [], [], []
for ln in open(sys.argv[1]):
    if not ln.startswith("BENCHRES"):
        continue
    d = dict(re.findall(r"(\w+)=(\S+)", ln)); n = int(d["op0"], 16)
    o, i, res = counts(n)
    if int(d["completed"]) != int(d["n"]) or int(d["odata"], 16) != res or int(d["mism_st"], 16) & 1:
        bad.append(n); continue
    X.append([1.0, o, i, 0.0 if res or n < 4 else 1.0]); y.append(fclk * int(d["latmin"]))
beta, rms = lstsq(X, y)
print("isprime cost model, %d batches (left out: %s), ns: base %.1f  per OUTER trial %.1f  per INNER shift step %.1f  "
      "composite-return %.1f  rms %.1f" % (len(X), bad or "none", *beta, rms))
