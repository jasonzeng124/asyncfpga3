#!/usr/bin/env python3
"""band_fit_own.py (audit T16): the band calibration from the owner's measured ring periods, own arithmetic.
    python3 -I band_fit_own.py measured.tsv pred.tsv
Band-mode delays are fast_min + x (slow_max - fast_min) arc by arc, so a ring's period is linear in x:
x_ring = (measured - FAST) / (SLOW - FAST). Prints per-ring x statistics, the global fit, errors at x = 0.38 and at
the fitted x, and the held-out splits (fit on one half, predict the other)."""
import csv, sys, statistics as st
M = {}
for r in csv.DictReader(open(sys.argv[1]), delimiter="\t"):
    M["g%s.b%s" % (r["g"], r["b"])] = (int(r["links"]), float(r["measured_ps"]))
P = {}
for r in csv.DictReader(open(sys.argv[2]), delimiter="\t"):
    P[r["ring"]] = (int(r["links"]), float(r["xray_fastmin_ps"]), float(r["xray_slowmax_ps"]))
keys = sorted(M, key=lambda k: (int(k[1:].split(".")[0]), int(k.split("b")[1])))
assert set(keys) == set(P), "ring sets differ"
assert all(M[k][0] == P[k][0] for k in keys), "link counts differ"
xs = {k: (M[k][1] - P[k][1]) / (P[k][2] - P[k][1]) for k in keys}
inside = sum(P[k][1] <= M[k][1] <= P[k][2] for k in keys)
v = sorted(xs.values()); q = lambda p: v[int(p * (len(v) - 1))]
print("rings %d, measured inside [FAST, SLOW]: %d" % (len(keys), inside))
print("per-ring x: median %.4f p05 %.4f p95 %.4f min %.4f max %.4f" % (st.median(v), q(.05), q(.95), v[0], v[-1]))
for L in (7, 15, 31, 63):
    print("  links %2d: median x %.4f" % (L, st.median([xs[k] for k in keys if M[k][0] == L])))
def err(x, ks):
    e = [(P[k][1] + x * (P[k][2] - P[k][1])) / M[k][1] - 1 for k in ks]
    return st.median(e), max(abs(t) for t in e)
def fit(ks): return st.median([xs[k] for k in ks])
for x in (0.38, fit(keys)):
    m, w = err(x, keys); print("x = %.4f: median error %+.2f%%, worst ring %.2f%%" % (x, 100 * m, 100 * w))
g = lambda k: int(k[1:].split(".")[0])
splits = {"groups 0-7 -> 8-15": ([k for k in keys if g(k) < 8], [k for k in keys if g(k) >= 8]),
          "groups 8-15 -> 0-7": ([k for k in keys if g(k) >= 8], [k for k in keys if g(k) < 8]),
          "7,15 -> 31,63": ([k for k in keys if M[k][0] <= 15], [k for k in keys if M[k][0] > 15]),
          "31,63 -> 7,15": ([k for k in keys if M[k][0] > 15], [k for k in keys if M[k][0] <= 15])}
for name, (a, b) in splits.items():
    x = fit(a); m, w = err(x, b)
    print("held-out %-20s fit x %.4f: median %+.2f%%, worst %.2f%%" % (name, x, 100 * m, 100 * w))
