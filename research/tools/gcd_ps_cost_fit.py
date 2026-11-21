#!/usr/bin/env python3
"""gcd_ps_cost_fit.py RUN_LOG [RUN_LOG ...] -- gcd's per-loop cost model, fitted to a gcd_ps GLS run.

    python3 research/tools/gcd_ps_cost_fit.py $S/psv1000/max/run_c*.log

Same model and counters as cells/hw/gcd_cost_fit.py / gcd_cost.sh (the August board fit):

    latency = base + k1*k_loop + k2*pre_ctz + k3*main + k4*inner_ctz

with the counters replayed from the C (dynamatic gcd.c, as gcd_cost.sh does) for each vector.  The latency is
taken from the GLS itself: the out0 bundling monitor's BUNDLE_REQ time (out0_req rising at its driver pin,
exact) minus the PS7 model's t_req (start of the CTRL write that raises the kernel's request).  The AXI write
latency between the two is a constant and lands in `base`, so base is NOT comparable with the board's (which
includes the bench harness); the four per-iteration costs are.
"""
import math, re, sys


def counters(a, b):
    k = cp = mn = ci = 0
    if a == 0 or b == 0:
        return k, cp, mn, ci
    while ((a | b) & 1) == 0:
        a >>= 1; b >>= 1; k += 1
    while a > 0 and (a & 1) == 0:
        a >>= 1; cp += 1
    while b > 0 and (b & 1) == 0:
        b >>= 1; cp += 1
    while a != 0:
        mn += 1
        diff = a - b
        if a < b:
            b = a
        a = diff if diff >= 0 else -diff
        while a > 0 and (a & 1) == 0:
            a >>= 1; ci += 1
    return k, cp, mn, ci


def lstsq(X, y):
    n = len(X[0])
    XtX = [[sum(r[i] * r[j] for r in X) for j in range(n)] for i in range(n)]
    Xty = [sum(r[i] * v for r, v in zip(X, y)) for i in range(n)]
    M = [XtX[i][:] + [1.0 if c == i else 0.0 for c in range(n)] + [Xty[i]] for i in range(n)]
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
    res = [v - sum(b * x for b, x in zip(beta, r)) for r, v in zip(X, y)]
    s2 = sum(e * e for e in res) / (len(X) - n)
    return beta, [math.sqrt(s2 * inv[i][i]) for i in range(n)], math.sqrt(s2)


def main():
    X, y, skipped = [], [], 0
    for path in sys.argv[1:]:
        reqs, res = [], []
        for ln in open(path):
            m = re.match(r"BUNDLE_REQ n=(\d+) margin=-?\d+ ps data=\S+ t=(\d+)", ln)
            if m:
                reqs.append(int(m.group(2)))
            m = re.match(r"PSRES vec=\d+ a=(\w+) b=(\w+) got=\S+ exp=\S+ (\w+) t_req=(\d+)", ln)
            if m:
                res.append((int(m.group(1), 16), int(m.group(2), 16), m.group(3), int(m.group(4))))
        if len(reqs) != len(res):
            sys.exit("%s: %d out0 requests vs %d results -- cannot pair them" % (path, len(reqs), len(res)))
        for (a, b, ok, t_req), t_out in zip(res, reqs):
            if ok != "OK" or t_out < t_req:
                skipped += 1
                continue
            k, cp, mn, ci = counters(a, b)
            X.append([1.0, k, cp, mn, ci]); y.append((t_out - t_req) / 1000.0)   # ns
    beta, se, rms = lstsq(X, y)
    names = ["base (AXI write + entry + exit)", "per k loop iteration", "per pre-loop ctz shift",
             "per MAIN loop iteration", "per inner ctz shift"]
    print("gcd cost model on %d vectors (%d skipped)" % (len(X), skipped))
    for n, b, s in zip(names, beta, se):
        print("  %-34s %8.1f +- %5.1f ns" % (n, b, s))
    print("  residual RMS %.1f ns" % rms)


if __name__ == "__main__":
    main()
