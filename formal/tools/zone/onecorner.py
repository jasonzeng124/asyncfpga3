"""onecorner.py -- probe C-12d: C-12c's bd_arbiter questions re-run with ONE
consistent prjxray corner and with the corner model, in dense time (TChecker).

C-12b/12c used O6 rise 56 / fall 124 and O5 rise 52 / fall 28 ps.  The 56/124
pair is prjxray's FAST_MAX and SLOW_MAX of one arc (makesdf.py:63:
(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)); nothing in prjxray-db separates
rise from fall; 28 has no prjxray source at all.  Here every LUT output gets
ONE delay interval used for both edges:

  arcs   O6 (ugrant g2, ustate q, ua1/ua2)   O5 (ugrant g1, ustate R0)
  FAST   [45, 56]                           [42, 55]
  SLOW   [100, 124]                         [121, 152]
  FASTp  56 (point)                         52 (point; the q pin I2)
  SLOWp  124 (point)                        150 (point; I2)
  CM(c,k) [(1-k)D6(c), (1+k)D6(c)]           [(1-k)D5(c), (1+k)D5(c)]
          D6(c) = lerp(56, 124, c), D5(c) = lerp(55, 152, c)
          (A's corner model: shared corner c, local scatter k; bounds rounded
          outward to 0.1 ps)

Interval rows draw each transition's delay independently in the interval, so
they allow rise != fall INSIDE one corner's band (a superset of rise = fall).
Point rows are exactly rise = fall.  O5 per-pin arcs are lumped per output
(union over pins I0..I2), as in 12b/12c.

Everything else is C-12c's arb.py model, unchanged (nodes, INITs, monitors,
environment: clients fall [c_lo, c_lo+20] after A, c_lo = 4; server follows
R0 after [s_lo, s_lo+20]; reset release [0, 8]).  Each configuration is ONE
full zone exploration (tckmodel.explore_all) answering every property.

Run:  python3 -I onecorner.py <section> [inertial|transport]
  sections: srv (server latency), wa (A0 fork, rising edge), wqg (q->ugrant
  route, HELD and UNHELD), all.   Results go to stdout.
"""
import math
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tckmodel import Circuit, lut, V, NOT, AND, C, ITE, explore_all  # noqa
from arb import (INIT_STATE_HELD, INIT_STATE_UNHELD, INIT_GRANT, INIT_C2,
                 props)  # noqa

U = 10          # model units per ps (0.1 ps resolution)


def cm(c, k):
    d6 = 56 + c * (124 - 56)
    d5 = 55 + c * (152 - 55)
    return dict(o6=((1 - k) * d6, (1 + k) * d6), o5=((1 - k) * d5, (1 + k) * d5))


CORNERS = {
    "FAST": dict(o6=(45, 56), o5=(42, 55)),
    "SLOW": dict(o6=(100, 124), o5=(121, 152)),
    "FASTp": dict(o6=(56, 56), o5=(52, 52)),
    "SLOWp": dict(o6=(124, 124), o5=(150, 150)),
    "CM0k20": cm(0, 0.2),
    "CM.5k20": cm(0.5, 0.2),
    "CM1k20": cm(1, 0.2),
    "CM.5k085": cm(0.5, 0.085),
}


def S(x):
    return (math.floor(x[0] * U + 1e-9),
            None if x[1] is None else math.ceil(x[1] * U - 1e-9))


def build(arcs, held=True, wq_s=(0, 0), wq_g=(0, 0), wa=(0, 0),
          srv=(160, 180), cli=(4, 24), mode="inertial", K=3):
    """C-12c arb.build with one interval per LUT output for both edges."""
    tp = dict(mode=mode, K=K)
    o6, o5 = S(arcs["o6"]), S(arcs["o5"])
    wq_s, wq_g, wa, srv, cli = S(wq_s), S(wq_g), S(wa), S(srv), S(cli)
    c = Circuit()
    for f in ("bad_ho", "bad_tx", "tok"):
        c.flag(f)
    st = INIT_STATE_HELD if held else INIT_STATE_UNHELD
    pins_s = ["r1", "r2", "qs", "rst", "A0s", "1"]
    pins_g = ["r1", "r2", "qg", None, None, "1"]
    c.add("rst", C(0), True, (0, 0), S((0, 8)))
    c.add("q", lut(st, pins_s, "O6"), False, o6, o6, **tp)
    c.add("R0", lut(st, pins_s, "O5"), False, o5, o5, **tp)
    c.add("qs", V("q"), False, wq_s, wq_s, **tp)
    c.add("qg", V("q"), False, wq_g, wq_g, **tp)
    c.add("A0s", V("A0"), False, wa, wa, **tp)
    ho = lambda g: AND(NOT(V(g)), V("A0"), NOT(V("tok")))  # noqa: E731
    c.add("g1", lut(INIT_GRANT, pins_g, "O5"), False, o5, o5, **tp,
          on_fire=[("bad_ho", ho("g1"))])
    c.add("g2", lut(INIT_GRANT, pins_g, "O6"), False, o6, o6, **tp,
          on_fire=[("bad_ho", ho("g2"))])
    for i in (1, 2):
        a = f"A{i}"
        c.add(a, lut(INIT_C2, [f"g{i}", "A0", a, "rst"]), False, o6, o6, **tp,
              on_fire=[("bad_tx", AND(NOT(V(a)), NOT(V("tok"))))],
              on_fire_set=[("tok", ITE(V(a), V("tok"), C(0)))])
    c.add("A0", V("R0"), False, srv, srv,
          on_fire_set=[("tok", ITE(V("A0"), V("tok"), C(1)))])
    for i in (1, 2):
        c.add(f"r{i}", ITE(V("rst"), V(f"r{i}"), NOT(V(f"A{i}"))), False,
              (0, None), cli)
    return c


KEYS = {"inertial": ["mutex", "amutex", "ho", "tx", "reach1", "reach2"],
        "transport": ["mutex", "amutex", "ho", "tx", "mutex_nr", "amutex_nr",
                      "ho_nr", "tx_nr", "mutex_nra", "amutex_nra", "ho_nra",
                      "tx_nra", "ovf", "ovf_nr", "reach1", "reach2"]}

CACHE = {}


def run(cor, mode, **kw):
    key = (cor, mode, tuple(sorted(kw.items())))
    if key in CACHE:
        return CACHE[key]
    r = explore_all(build(CORNERS[cor], mode=mode, **kw), props(mode),
                    mem_gb=3.0, timeout=3600)
    p = r.get("props")
    if p is None:
        print("   ERR", cor, mode, kw, r.get("err", "")[-300:], flush=True)
        p = {}
    CACHE[key] = (p, r)
    return CACHE[key]


def fmt(p, mode):
    return " ".join(f"{k}={p.get(k, '?')}" for k in KEYS[mode] if k in p)


def sweep(cor, mode, param, mk, xs, keys, label, **kw):
    """evaluate at each x; then for every key whose verdict changes between
    neighbouring x, bisect to 0.1 ps.  Prints the grid and the edges."""
    res = {}
    for x in xs:
        p, r = run(cor, mode, **mk(x), **kw)
        res[x] = p
        print(f"  [{mode[:4]}] {cor:9} {label} {param}={x:7}  {fmt(p, mode)}"
              f"  zones={r.get('VISITED_STATES')} {r['seconds']:.1f}s",
              flush=True)
    edges = []
    for k in keys:
        xs_ok = [x for x in xs if k in res[x]]
        for a, b in zip(xs_ok, xs_ok[1:]):
            if res[a][k] != res[b][k]:
                lo, hi = a, b
                while hi - lo > 0.1 + 1e-9:
                    mid = round((lo + hi) / 2, 1)
                    if mid in (lo, hi):
                        break
                    pm, _ = run(cor, mode, **mk(mid), **kw)
                    if pm.get(k) == res[a][k]:
                        lo = mid
                    else:
                        hi = mid
                edges.append((k, lo, hi, res[a][k], res[b][k]))
                print(f"   EDGE {cor:9} {label} {k}: {param}={lo} -> {res[a][k]}"
                      f", {param}={hi} -> {res[b][k]}", flush=True)
    return res, edges


SRV = [0, 4, 20, 40, 60, 80, 120, 160, 240, 320]
WA = [0, 32, 64, 96, 128, 160, 200, 240, 280, 320, 400]
WQ = [0, 8, 16, 24, 40, 56, 80, 120, 160]


def sec_srv(mode, cors):
    print(f"== server latency s_lo (window [s_lo, s_lo+20] ps), zero routing, {mode} ==")
    keys = [k for k in KEYS[mode] if not k.startswith("reach")]
    for cor in cors:
        for held in (True, False):
            sweep(cor, mode, "s_lo", lambda s: dict(srv=(s, s + 20)), SRV, keys,
                  "HELD  " if held else "UNHELD", held=held)


def sec_wa(mode, cors):
    print(f"== A0 fork (A0 reaches ustate.I4 wa ps late), HELD, srv [160,180], {mode} ==")
    keys = [k for k in KEYS[mode] if not k.startswith("reach")]
    for cor in cors:
        sweep(cor, mode, "wa", lambda w: dict(wa=(w, w)), WA, keys, "HELD  ")
        sweep(cor, mode, "wa", lambda w: dict(wa=(w, w)), WA, keys,
              "HELD c_lo=40", cli=(40, 60))


def sec_wqg(mode, cors):
    print(f"== q->ugrant route wq_g (wq_s = 0), srv [160,180], {mode} ==")
    keys = [k for k in KEYS[mode] if not k.startswith("reach")]
    for cor in cors:
        for held in (True, False):
            sweep(cor, mode, "wq_g", lambda w: dict(wq_g=(w, w)), WQ, keys,
                  "HELD  " if held else "UNHELD", held=held)
    if mode == "transport":
        print("== HELD transport, wq_s = 16: does only the skew wq_g - wq_s matter? ==")
        for cor in cors:
            sweep(cor, mode, "wq_g", lambda w: dict(wq_g=(w, w), wq_s=(16, 16)),
                  [0, 8, 16, 24, 40, 80], keys, "HELD wq_s=16")


def sec_tp(mode, cors):
    """slim transport section (HELD only, coarse grids): the full grids of
    srv/wa/wqg take minutes per row in transport mode."""
    keys = [k for k in KEYS[mode] if not k.startswith("reach")]
    for cor in cors:
        print(f"== {cor} HELD transport: server latency ==", flush=True)
        sweep(cor, mode, "s_lo", lambda s: dict(srv=(s, s + 20)), [160, 60, 20],
              keys, "HELD  ")
        print(f"== {cor} HELD transport: A0 fork ==", flush=True)
        sweep(cor, mode, "wa", lambda w: dict(wa=(w, w)),
              [0, 100, 128, 200, 240, 300], keys, "HELD  ")
        print(f"== {cor} HELD transport: q->ugrant route (wq_s = 0, then 16) ==", flush=True)
        sweep(cor, mode, "wq_g", lambda w: dict(wq_g=(w, w)), [0, 8, 24, 80, 160],
              keys, "HELD  ")
        sweep(cor, mode, "wq_g", lambda w: dict(wq_g=(w, w), wq_s=(16, 16)),
              [0, 16, 24, 80], keys, "HELD wq_s=16")


if __name__ == "__main__":
    t0 = time.time()
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    mode = sys.argv[2] if len(sys.argv) > 2 else "inertial"
    cors = sys.argv[3].split(",") if len(sys.argv) > 3 else list(CORNERS)
    print("arcs (ps):", {k: CORNERS[k] for k in cors})
    for s in (("srv", "wa", "wqg") if what == "all" else (what,)):
        globals()["sec_" + s](mode, cors)
    print(f"total {time.time()-t0:.1f} s")
