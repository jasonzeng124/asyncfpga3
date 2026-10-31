"""arb.py -- bd_arbiter (cells/rtl/bd_arb.v) as timed automata, checked by Storm.

Nodes (each an inertial bounded-delay timed automaton, see tamodel.py).  Time
unit: 1 tick = 4 ps.  LUT arcs from the header's zero-routing trace
(verify/probes/arb_handover.v): O6 rise 56 ps, O6 fall 124 ps, O5 rise 52 ps,
O5 fall 28 ps  ->  14, 31, 13, 7 ticks.  Each arc gets [nom-spread, nom+spread].

  rst      reset release, starts 1, falls in [0, 2]
  q        ustate O6: INIT 64'hFFF0_FFB2_ACAC_ACAC (held, as shipped) or the
           UNHELD node (O6 half = bd_c2n_set's FFB2_FFB2, I4 ignored),
           pins I0=r1 I1=r2 I2=qs I3=rst I4=A0s I5=1
  R0       ustate O5, same pins
  qs, qg   routed copies of q at ustate.I2 and ugrant.I2 (wire [lo,hi])
  A0s      routed copy of A0 at ustate.I4 (wire [lo,hi]); ua1/ua2 read A0
  g1, g2   ugrant O5/O6: INIT 64'h0C0C_0C0C_A0A0_A0A0, I0=r1 I1=r2 I2=qg I5=1
  A1, A2   bd_c2 INIT 64'h00E8_..., I0=g, I1=A0, I2=own output, I3=rst
  A0       the server: four-phase, follows R0 with latency [s_lo, s_hi]
  r1, r2   clients: after reset, r follows !A; rise at ANY time (no
           deadline: free), fall [c_lo, c_hi] after A rises
Monitors:
  mutex    g1 & g2 reachable
  amutex   A1 & A2 reachable
  ho       a grant rises while A0 is still high from a transaction that
           has already been acknowledged (the header's handover finding)
  tx       a client is acknowledged with no server transaction (A0 rise)
           since the previous acknowledge (80 completions vs 40 transactions)
  reach1/2 non-vacuity: A1 resp. A2 can rise
Run:  <venv>/bin/python -I arb.py
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tamodel import Circuit, lut, var, check  # noqa: E402

INIT_STATE_HELD = 0xFFF0_FFB2_ACAC_ACAC
# unheld: the O6 half replaced by bd_c2n_set's function (I4 ignored)
INIT_STATE_UNHELD = 0xFFB2_FFB2_ACAC_ACAC
INIT_GRANT = 0x0C0C_0C0C_A0A0_A0A0
INIT_C2 = 0x00E8_00E8_00E8_00E8

O6R, O6F, O5R, O5F = 14, 31, 13, 7      # ticks of 4 ps


def iv(nom, spread):
    return (max(nom - spread, 0), nom + spread)


def build(held=True, spread=0, wq_s=(0, 0), wq_g=(0, 0), wa=(0, 0),
          srv=(1, 6), cli=(1, 6), mode="inertial"):
    """mode applies to every LUT output and routed wire (inertial or
    transport); the environment (rst, server A0, clients) stays inertial."""
    tp = dict(mode=mode, K=3)
    c = Circuit()
    for f in ("bad_ho", "bad_tx", "tok"):
        c.flag(f)
    st = INIT_STATE_HELD if held else INIT_STATE_UNHELD
    pins_s = ["r1", "r2", "qs", "rst", "A0s", "1"]
    pins_g = ["r1", "r2", "qg", None, None, "1"]
    c.add("rst", lambda env: "false", True, (0, 0), (0, 2))
    c.add("q", lut(st, pins_s, "O6"), False, iv(O6R, spread), iv(O6F, spread),
          pending0=(mode == "transport"), **tp)
    c.add("R0", lut(st, pins_s, "O5"), False, iv(O5R, spread), iv(O5F, spread),
          **tp)
    c.add("qs", var("q"), False, wq_s, wq_s, **tp)
    c.add("qg", var("q"), False, wq_g, wq_g, **tp)
    c.add("A0s", var("A0"), False, wa, wa, **tp)
    c.add("g1", lut(INIT_GRANT, pins_g, "O5"), False,
          iv(O5R, spread), iv(O5F, spread), **tp,
          on_fire=[("bad_ho", lambda env: "!g1 & A0 & !tok")])
    c.add("g2", lut(INIT_GRANT, pins_g, "O6"), False,
          iv(O6R, spread), iv(O6F, spread), **tp,
          on_fire=[("bad_ho", lambda env: "!g2 & A0 & !tok")])
    for i in (1, 2):
        c.add(f"A{i}", lut(INIT_C2, [f"g{i}", "A0", f"A{i}", "rst"]), False,
              iv(O6R, spread), iv(O6F, spread), **tp,
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


PROPS = {"mutex": "Pmax=? [F g1 & g2]",
         "amutex": "Pmax=? [F A1 & A2]",
         "ho": "Pmax=? [F bad_ho]",
         "tx": "Pmax=? [F bad_tx]",
         "reach1": "Pmax=? [F A1]",
         "reach2": "Pmax=? [F A2]"}


OVF = "Pmax=? [F " + " | ".join(f"ovf_{n}" for n in
                              ("q", "R0", "qs", "qg", "A0s", "g1", "g2",
                               "A1", "A2")) + "]"
MODE = "inertial"


def row(label, **kw):
    kw.setdefault("mode", MODE)
    props = dict(PROPS)
    if kw["mode"] == "transport":
        props["ovf"] = OVF
        # the same properties restricted to runs with no runt on the decision
        # node q (no second edge ever queued on q): separates tier 3
        # (metastable/runt q, not excludable) from the digital races
        props["ovf_nr"] = "Pmax=? [F !mlt_q & (" + OVF[len("Pmax=? [F "):-1] + ")]"
        for k in ("mutex", "amutex", "ho", "tx"):
            inner = PROPS[k][len("Pmax=? [F "):-1]
            props[k + "_nr"] = f"Pmax=? [F !mlt_q & ({inner})]"
    label = f"[{kw['mode'][:4]}] " + label
    r, ns, nt, sec = check(build(**kw).prism(), props)
    vals = " ".join(f"{k}={v:.0f}" for k, v in r.items())
    print(f"{label:46} {vals}  states={ns} trans={nt} {sec:.1f}s", flush=True)
    return r


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "dump":
        print(build().prism())
        sys.exit()
    t0 = time.time()
    if len(sys.argv) > 1:
        MODE = sys.argv[1]
    print("== 1. grant overlap, UNHELD, nominal arcs: q->ugrant wire needed ==")
    for w in range(0, 7):
        row(f"UNHELD wq_g={w} ({4*w} ps) srv=[40,45]", held=False,
            wq_g=(w, w), srv=(40, 45))
    print("== 2. server latency sweep (nominal arcs, zero routing) ==")
    for held in (False, True):
        for s in ((1, 5, 10, 20, 30, 40, 60) if MODE == "inertial"
                  else (10, 15, 20, 40)):
            row(f"{'HELD' if held else 'UNHELD'} srv=[{s},{s+5}]",
                held=held, srv=(s, s + 5))
    print("== 3. HELD: A0 fork skew (A0 reaches ustate.I4 late) ==")
    for w in (0, 8, 16, 24, 32, 48):
        row(f"HELD wa={w} srv=[40,45]", held=True, wa=(w, w), srv=(40, 45))
    print("== 4. arc spread +-2 ticks, routed q in [0,8], A0 fork [0,4] ==")
    # transport + spread: > 20 min and > 5 GB (OOM-killed in this sandbox)
    for held in ((False, True) if MODE == "inertial" else ()):
        row(f"{'HELD' if held else 'UNHELD'} spread=2 srv=[40,45]",
            held=held, spread=2, wq_g=(0, 8), wq_s=(0, 8), wa=(0, 4),
            srv=(40, 45))
    print("== 5. exact break points ==")
    for s in (range(14, 21) if MODE == "inertial" else (14, 15)):
        row(f"HELD srv=[{s},{s+5}]", held=True, srv=(s, s + 5))
    for w in (range(24, 33) if MODE == "inertial" else (24, 28, 29, 32)):
        row(f"HELD wa={w} srv=[40,45]", held=True, wa=(w, w), srv=(40, 45))
    for w in range(24, 33, 2):
        row(f"HELD wa={w} wq_g=6 srv=[40,45]", held=True, wa=(w, w),
            wq_g=(6, 6), srv=(40, 45))
    print(f"total {time.time()-t0:.1f} s")
