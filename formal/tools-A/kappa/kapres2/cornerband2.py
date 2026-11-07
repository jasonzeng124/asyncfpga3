#!/usr/bin/env python3
"""cornerband2.py -- corner-model band file for one corner CELL [ca, cb] and scatter kappa.

    python3 cornerband2.py FAST.bands.json SLOW.bands.json CA CB KAPPA OUT.bands.json

kapres/cornerband.py with two changes (KapRes2):
  * the inputs are VALIDATED (check_bands.check: every band a pair of naturals with lo <= hi);
    an inverted band is REJECTED (exit 1), never hulled or narrowed.  The committed FAST files
    fail this (prjxray BRKH_INT, A-kapres2.md); run check_bands.py fix first.
  * the global lut / route fields use the same min/max formula as every arc (cornerband.py took
    F[0], S[0] at CA for lo and F[1], S[1] at CB for hi, which is not the min/max when S < F).
The per-arc band is exactly Formal/Core/Delay/CornerCell.lean's cellLo / cellHi:
    lo = floor((1-kappa) * min(lerp(f0,s0,CA), lerp(f0,s0,CB)))
    hi = ceil ((1+kappa) * max(lerp(f1,s1,CA), lerp(f1,s1,CB)))
with fast band [f0, f1], slow band [s0, s1], lerp(f,s,c) = (1-c) f + c s, exact rationals.
CornerCell.cell_band_int / realizes_cell: for every corner c in [CA, CB] (0 <= CA, CB <= 1),
every true endpoint F in [f0,f1], S in [s0,s1] and every delay d with
(1-kappa) lerp(F,S,c) <= d <= (1+kappa) lerp(F,S,c), lo <= d <= hi.
The output is validated too.
"""
import json
import math
import os
import sys
from fractions import Fraction as Q

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_bands import check  # noqa: E402

lerp = lambda f, s, c: (1 - c) * f + c * s


def cell(f, s, ca, cb, k):
    (f0, f1), (s0, s1) = f, s
    lo = math.floor((1 - k) * min(lerp(Q(f0), Q(s0), ca), lerp(Q(f0), Q(s0), cb)))
    hi = math.ceil((1 + k) * max(lerp(Q(f1), Q(s1), ca), lerp(Q(f1), Q(s1), cb)))
    return [lo, hi]


def main():
    fp, sp, ca, cb, k, outp = sys.argv[1:7]
    ca, cb, k = Q(ca), Q(cb), Q(k)
    assert 0 <= ca <= cb <= 1 and 0 <= k <= 1
    for p in (fp, sp):
        bad = check(p)
        if bad:
            sys.exit("cornerband2: REJECT %s: %d invalid band(s), first %s" % (p, len(bad), bad[0]))
    F = json.load(open(fp))
    S = json.load(open(sp))
    out = dict(S)
    out["comment"] = ("corner-model band (kapres2/cornerband2.py): corner cell [%s,%s], kappa %s, "
                      "from %s + %s" % (ca, cb, k, fp.split('/')[-1], sp.split('/')[-1]))
    for sec in ("cells", "arcs"):
        assert set(F[sec]) == set(S[sec]), sec
        out[sec] = {key: cell(F[sec][key], S[sec][key], ca, cb, k) for key in S[sec]}
    for key in ("lut", "route"):
        if key in S and key in F:
            out[key] = cell(F[key], S[key], ca, cb, k)
    json.dump(out, open(outp, "w"))
    bad = check(outp)
    if bad:
        sys.exit("cornerband2: output %s invalid: %s" % (outp, bad[0]))


if __name__ == "__main__":
    main()
