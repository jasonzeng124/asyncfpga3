#!/usr/bin/env python3
"""spot.py -- spot values of kapres/cornerband.py's per-arc formula, emitted as Lean `example`s
for Formal/Core/Delay/CornerCell.lean (section 5). Same arithmetic as cornerband.py."""
import math
from fractions import Fraction as Q

lerp = lambda f, s, c: (1 - c) * f + c * s


def band(f0, f1, s0, s1, ca, cb, k):
    flo, fhi = min(f0, f1), max(f0, f1)
    slo, shi = min(s0, s1), max(s0, s1)
    lo = math.floor((1 - k) * min(lerp(Q(flo), Q(slo), ca), lerp(Q(flo), Q(slo), cb)))
    hi = math.ceil((1 + k) * max(lerp(Q(fhi), Q(shi), ca), lerp(Q(fhi), Q(shi), cb)))
    return lo, hi


CASES = [  # (f0, f1, s0, s1, ca, cb, kappa)
    (95, 103, 211, 230, Q(1, 8), Q(1, 4), Q(1, 10)),
    (412, 377, 905, 951, Q(0), Q(1, 16), Q(906, 10000)),   # inverted fast band (lo > hi)
    (1, 1, 2, 3, Q(3, 32), Q(1, 8), Q(5, 100)),
    (240, 260, 233, 250, Q(7, 8), Q(1), Q(1, 10)),         # S < F: lerp decreasing
]


def lean(q):
    return "(%d/%d : ℚ)" % (q.numerator, q.denominator)


for f0, f1, s0, s1, ca, cb, k in CASES:
    lo, hi = band(f0, f1, s0, s1, ca, cb, k)
    args = "%d %d %d %d %s %s %s" % (f0, f1, s0, s1, lean(ca), lean(cb), lean(k))
    print("example : cellLo %s = %d := by decide" % (args, lo))
    print("example : cellHi %s = %d := by decide" % (args, hi))
