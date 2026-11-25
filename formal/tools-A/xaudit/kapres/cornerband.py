#!/usr/bin/env python3
"""cornerband.py -- corner-model band file for one corner CELL [ca, cb] and scatter kappa.

    python3 cornerband.py FAST.bands.json SLOW.bands.json CA CB KAPPA OUT.bands.json

Model (Formal/Core/Delay/Corner.lean, ℕ form Substrate/CornerNat.lean):
  H-affine     nominal delay of arc e at corner c in [0,1] is lerp(F_e, S_e, c) = (1-c)F_e + c S_e;
  SharedCorner one c for every arc;
  Scat kappa   (1-kappa)·nominal <= d <= (1+kappa)·nominal.
The prjxray endpoints of one arc are known only up to each corner's [MIN, MAX]
(F_e in [FAST_MIN, FAST_MAX], S_e in [SLOW_MIN, SLOW_MAX]); we take the union over
those choices.  Inputs: the committed one-corner band files (fast = [FAST_MIN, FAST_MAX],
slow = [SLOW_MIN, SLOW_MAX], both already rounded outward to whole ps by routed2x.py).
For every c in [CA, CB] (CA <= CB) and every admissible F_e, S_e, the delay lies in
    [ floor((1-kappa)·lerp(FAST_MIN, SLOW_MIN, CA)),  ceil((1+kappa)·lerp(FAST_MAX, SLOW_MAX, CB)) ]
(written for F <= S; in general the lo end is the min of the affine lerp over {CA, CB} and the hi
end the max, which is what is computed): an affine function of c attains its extrema on [CA, CB]
at CA or CB, and lerp(F,S,c) is nondecreasing in F and in S for c in [0,1].
Exact rational arithmetic, rounded outward to whole ps.
DATA QUIRK: a few committed FAST bands have lo > hi (prjxray FAST_MIN > FAST_MAX on 2-20 arcs per
seed); Parse.toSteps already reads such a band as [lo, lo].  Here the fast endpoint is taken as the
hull [min, max] of the two numbers, which contains both readings (sound).
CA = CB = 0, kappa = 0 reproduces FAST (with that hull); CA = CB = 1 reproduces SLOW exactly.
"""
import json
import math
import sys
from fractions import Fraction as Q


def main():
    fp, sp, ca, cb, k, outp = sys.argv[1:7]
    ca, cb, k = Q(ca), Q(cb), Q(k)
    assert 0 <= ca <= cb <= 1 and 0 <= k <= 1
    F = json.load(open(fp))
    S = json.load(open(sp))
    out = dict(S)
    out["comment"] = ("corner-model band (kapres/cornerband.py): corner cell [%s,%s], kappa %s, "
                      "from %s + %s" % (ca, cb, k, fp.split('/')[-1], sp.split('/')[-1]))
    lerp = lambda f, s, c: (1 - c) * f + c * s
    for sec in ("cells", "arcs"):
        assert set(F[sec]) == set(S[sec]), sec
        o = {}
        for key, (slo, shi) in S[sec].items():
            f0, f1 = F[sec][key]
            flo, fhi = min(f0, f1), max(f0, f1)
            slo, shi = min(slo, shi), max(slo, shi)
            lo = math.floor((1 - k) * min(lerp(Q(flo), Q(slo), ca), lerp(Q(flo), Q(slo), cb)))
            hi = math.ceil((1 + k) * max(lerp(Q(fhi), Q(shi), ca), lerp(Q(fhi), Q(shi), cb)))
            o[key] = [lo, hi]
        out[sec] = o
    for key in ("lut", "route"):     # global summary fields: same construction
        if key in S and key in F:
            out[key] = [math.floor((1 - k) * lerp(Q(F[key][0]), Q(S[key][0]), ca)),
                        math.ceil((1 + k) * lerp(Q(F[key][1]), Q(S[key][1]), cb))]
    json.dump(out, open(outp, "w"))


if __name__ == "__main__":
    main()
