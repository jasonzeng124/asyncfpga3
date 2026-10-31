"""celem1c.py -- probe C-12d: C-12b/12c's bd_c2 environment-latency bound
instantiated at ONE consistent prjxray corner and in the corner model.

12b/12c's C-element runs already used one interval per arc for both edges
(dl, dw symmetric), so they never mixed corners.  This only instantiates the
bound with ps numbers: O = LUT6 O6 arc, qp = the routed feedback.
  FAST  dl = [45, 56]    dw = [60, 80]   (assumed feedback route, FAST)
  SLOW  dl = [100, 124]  dw = [150, 200] (same route, SLOW)
  CM    dl, dw = (1 -+ k) * lerp(FAST_MAX, SLOW_MAX, c), c = 0.5, k = 0.2
12c's claims: transport spec iff e_lo >= dw_hi; inertial spec iff
e_lo > dw_hi - dl_lo; inertial hazard-free iff e_lo > dw_hi.
C-12d fix: the environment's response window is [e_lo, inf) (independent
inputs, no upper bound).  The first version used [e_lo, e_lo + 30] ps; with
dl_lo > 30 ps the two inputs could then never be skewed by more than the LUT's
own delay, which hid the hazard (spec "held" for every e_lo: an artefact).
Corner model rows: dl from the O6 arc, dw from the assumed route bands above,
lit = [(1-k) D, (1+k) D], D = lerp(FAST_MIN, SLOW_MAX, c); cons = scatter on top
of the corner windows (B-arb-kappa readings).
Run:  python3 -I celem1c.py      (units 1 ps)
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from celem import build, props  # noqa: E402
from tckmodel import reach  # noqa: E402


import math


def lit(F, S, c, k):
    d = F + c * (S - F)
    return (math.floor((1 - k) * d), math.ceil((1 + k) * d))


def cons(fw, sw, c, k):
    return (math.floor((1 - k) * (fw[0] + c * (sw[0] - fw[0]))),
            math.ceil((1 + k) * (fw[1] + c * (sw[1] - fw[1]))))


DLF, DLS, DWF, DWS = (45, 56), (100, 124), (60, 80), (150, 200)
CASES = [("FAST", DLF, DWF), ("SLOW", DLS, DWS)]
for _c in (0, 1):
    CASES.append((f"lit c={_c} k=1/11", lit(DLF[0], DLS[1], _c, 1 / 11), lit(DWF[0], DWS[1], _c, 1 / 11)))
    CASES.append((f"cons c={_c} k=1/11", cons(DLF, DLS, _c, 1 / 11), cons(DWF, DWS, _c, 1 / 11)))

if __name__ == "__main__":
    t0 = time.time()
    for name, dl, dw in CASES:
        for mode in ("inertial", "transport"):
            keys = ["spec", "haz"] if mode == "inertial" else ["spec", "ovf"]
            first_ok = {}
            for k in keys:
                lo, hi = 0, dw[1] + 2          # bisection on e_lo (monotone)
                while lo < hi:
                    mid = (lo + hi) // 2
                    c = build(dl, dw, (mid, None), R=20, mode=mode)
                    rr = reach(c.tck(props(mode)[k]))["reachable"]
                    assert rr is not None, (name, mode, k, mid)
                    if rr:
                        lo = mid + 1
                    else:
                        hi = mid
                first_ok[k] = lo
            print(f"{name:16} {mode:9} dl={dl} dw={dw}: " +
                  " ".join(f"{k} holds iff e_lo >= {v}" for k, v in first_ok.items()) +
                  f"   (dw_hi={dw[1]}, dw_hi-dl_lo={dw[1]-dl[0]})", flush=True)
    print(f"total {time.time()-t0:.1f}s")
