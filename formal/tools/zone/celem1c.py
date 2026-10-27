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
Run:  python3 -I celem1c.py      (units 1 ps)
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from celem import build, props  # noqa: E402
from tckmodel import reach  # noqa: E402


def cm(f, s, c=0.5, k=0.2):
    d = f + c * (s - f)
    return (int((1 - k) * d), int(-(-(1 + k) * d // 1)))


CASES = [("FAST", (45, 56), (60, 80)), ("SLOW", (100, 124), (150, 200)),
         ("CM c=.5 k=.2", cm(56, 124), cm(80, 200))]

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
                    c = build(dl, dw, (mid, mid + 30), R=20, mode=mode)
                    if reach(c.tck(props(mode)[k]))["reachable"]:
                        lo = mid + 1
                    else:
                        hi = mid
                first_ok[k] = lo
            print(f"{name:13} {mode:9} dl={dl} dw={dw}: " +
                  " ".join(f"{k} holds iff e_lo >= {v}" for k, v in first_ok.items()) +
                  f"   (dw_hi={dw[1]}, dw_hi-dl_lo={dw[1]-dl[0]})", flush=True)
    print(f"total {time.time()-t0:.1f}s")
