"""onecorner.py -- probe C-12d: C-12b's Storm bd_arbiter checks re-run with ONE
consistent prjxray corner (rise = fall band) instead of 12b's mixed arcs
(O6 rise 56 / fall 124, O5 rise 52 / fall 28 ps; 56/124 are FAST_MAX/SLOW_MAX
of one arc, 28 has no prjxray source).  Cross-check of zone/onecorner.py on a
digital-clock grid.  1 tick = 4 ps; bounds rounded outward:

  FAST  O6 [45,56] -> [11,14]     O5 [42,55]  -> [10,14]
  SLOW  O6 [100,124] -> [25,31]   O5 [121,152] -> [30,38]

Model, monitors and environment are 12b's arb.py (inertial), with one interval
per LUT output used for both edges.  Ties are explored both ways (12b), so a
dense-time strict bound X shows as 'fails at X ticks'.
Run:  <venv>/bin/python -I onecorner.py
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tamodel import Circuit, lut, var, check  # noqa: E402
from arb import (INIT_STATE_HELD, INIT_STATE_UNHELD, INIT_GRANT, INIT_C2,
                 PROPS)  # noqa: E402

CORNERS = {"FAST": dict(o6=(11, 14), o5=(10, 14)),
           "SLOW": dict(o6=(25, 31), o5=(30, 38))}

# corner model (A's Corner.lean; B-arb-kappa readings), rounded outward to 4 ps ticks
PRJ = dict(o6=(45, 56, 100, 124), o5=(42, 55, 121, 152))


def _tk(lo, hi):
    import math
    return (math.floor(lo / 4 + 1e-9), math.ceil(hi / 4 - 1e-9))


for _c in (0, 1):
    for _kn, _k in (("k11", 1 / 11), ("kE", 383 / 1927)):
        CORNERS[f"lit{_c}{_kn}"] = {n: _tk((1 - _k) * (v[0] + _c * (v[3] - v[0])),
                                           (1 + _k) * (v[0] + _c * (v[3] - v[0])))
                                    for n, v in PRJ.items()}
        CORNERS[f"cons{_c}{_kn}"] = {n: _tk((1 - _k) * (v[0] + _c * (v[2] - v[0])),
                                            (1 + _k) * (v[1] + _c * (v[3] - v[1])))
                                     for n, v in PRJ.items()}


def build(arcs, held=True, wq_s=(0, 0), wq_g=(0, 0), wa=(0, 0),
          srv=(40, 45), cli=(1, 6)):
    tp = dict(mode="inertial", K=3)
    o6, o5 = arcs["o6"], arcs["o5"]
    c = Circuit()
    for f in ("bad_ho", "bad_tx", "tok"):
        c.flag(f)
    st = INIT_STATE_HELD if held else INIT_STATE_UNHELD
    pins_s = ["r1", "r2", "qs", "rst", "A0s", "1"]
    pins_g = ["r1", "r2", "qg", None, None, "1"]
    c.add("rst", lambda env: "false", True, (0, 0), (0, 2))
    c.add("q", lut(st, pins_s, "O6"), False, o6, o6, **tp)
    c.add("R0", lut(st, pins_s, "O5"), False, o5, o5, **tp)
    c.add("qs", var("q"), False, wq_s, wq_s, **tp)
    c.add("qg", var("q"), False, wq_g, wq_g, **tp)
    c.add("A0s", var("A0"), False, wa, wa, **tp)
    c.add("g1", lut(INIT_GRANT, pins_g, "O5"), False, o5, o5, **tp,
          on_fire=[("bad_ho", lambda env: "!g1 & A0 & !tok")])
    c.add("g2", lut(INIT_GRANT, pins_g, "O6"), False, o6, o6, **tp,
          on_fire=[("bad_ho", lambda env: "!g2 & A0 & !tok")])
    for i in (1, 2):
        c.add(f"A{i}", lut(INIT_C2, [f"g{i}", "A0", f"A{i}", "rst"]), False,
              o6, o6, **tp,
              on_fire=[("bad_tx", lambda env, i=i: f"!A{i} & !tok")],
              on_fire_set=[("tok", lambda env, i=i: f"A{i} ? tok : false")])
    c.add("A0", var("R0"), False, srv, srv,
          on_fire_set=[("tok", lambda env: "A0 ? tok : true")])
    for i in (1, 2):
        c.add(f"r{i}",
              lambda env, i=i: (f"({env.get('rst', 'rst')} ? r{i} : "
                                f"!{env.get(f'A{i}', f'A{i}')})"),
              False, (0, None), cli)
    return c


def row(cor, label, **kw):
    r, ns, nt, sec = check(build(CORNERS[cor], **kw).prism(), PROPS)
    vals = " ".join(f"{k}={v:.0f}" for k, v in r.items())
    print(f"[iner] {cor} {label:34} {vals}  states={ns} {sec:.1f}s", flush=True)
    return r


if __name__ == "__main__":
    t0 = time.time()
    cors = sys.argv[1].split(",") if len(sys.argv) > 1 else list(CORNERS)
    print({c: CORNERS[c] for c in cors})
    for cor in cors:
        print(f"== {cor}: server latency (ticks of 4 ps), zero routing ==")
        for held in (True, False):
            for s in (0, 1, 2, 5, 10, 15, 20, 30, 40):
                row(cor, f"{'HELD' if held else 'UNHELD'} srv=[{s},{s+5}]",
                    held=held, srv=(s, s + 5))
        print(f"== {cor}: HELD A0 fork wa (ticks), srv [40,45] ==")
        for w in (0, 8, 16, 20, 22, 23, 24, 25, 26, 28, 32, 48, 50, 52, 54,
                  56, 58, 60, 64, 72):
            row(cor, f"HELD wa={w}", wa=(w, w))
        print(f"== {cor}: q->ugrant route wq_g (ticks), srv [40,45] ==")
        for held in (True, False):
            for w in (0, 2, 4, 6, 8, 10, 11, 12, 14, 20, 26, 30, 40):
                row(cor, f"{'HELD' if held else 'UNHELD'} wq_g={w}",
                    held=held, wq_g=(w, w))
    print(f"total {time.time()-t0:.1f} s")
