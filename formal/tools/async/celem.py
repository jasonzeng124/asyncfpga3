"""celem.py -- bd_c2 (cells/rtl/bd_ce.v) as timed automata, checked by Storm.

Nodes (one timed automaton each, inertial bounded delay, see tamodel.py):
  rst   one-shot reset release: starts 1, falls at some time in [0, R]
  O     the LUT6 output pin: REAL INIT 64'h00E8_00E8_00E8_00E8,
        pins I0=a I1=b I2=qp I3=rst I4=0 I5=0, delay [dl_lo, dl_hi]
  qp    the routed feedback net as seen at pin I2: buffer of O, [dw_lo, dw_hi]
  a, b  the environment: each input toggles after it sees O catch up with it
        (f = !O), latency [e_lo, e_hi] each, independently -- the
        speed-independent four-phase environment of a 2-input C-element.
Checks:
  spec  O changes only when a = b != O (C-element behaviour, pre-state)
  haz   O loses its excitation without firing (output-persistency / hazard)
  live  Pmin of O eventually rising (no deadlock / no stuck run)
Run:  <venv>/bin/python -I celem.py      (sweeps; prints a table)
"""
import itertools
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tamodel import Circuit, lut, var  # noqa: E402

INIT_C2 = 0x00E8_00E8_00E8_00E8


def build(dl, dw, e, R=2, init=INIT_C2):
    c = Circuit()
    c.flag("bad_spec")
    c.add("rst", lambda env: "false", True, (0, 0), (0, R))
    c.add("O", lut(init, ["a", "b", "qp", "rst"]), False, dl, dl,
          watch_hazard=True,
          on_fire=[("bad_spec",
                    lambda env: "!(a=b & a!=O)")])
    c.add("qp", var("O"), False, dw, dw)
    c.add("a", lambda env: f"!{env.get('O', 'O')}", False, e, e)
    c.add("b", lambda env: f"!{env.get('O', 'O')}", False, e, e)
    return c


PROPS = {"spec": 'Pmax=? [F bad_spec]',
         "haz": 'Pmax=? [F hz_O]',
         "live": 'Pmin=? [F O]'}


def run(dl, dw, e):
    c = build(dl, dw, e)
    return c.check_all(PROPS) if hasattr(c, "check_all") else None


if __name__ == "__main__":
    from tamodel import check
    if len(sys.argv) > 1 and sys.argv[1] == "dump":
        print(build((1, 2), (1, 3), (1, 4)).prism())
        sys.exit()
    print("dl        dw        e         spec haz  live  states  trans   sec")
    t_all = time.time()
    rows = []
    for dl in [(1, 1), (1, 3)]:
        for dw in [(1, 1), (1, 3), (2, 4)]:
            for elo in range(0, 6):
                for ehi in sorted({elo, elo + 3}):
                    e = (elo, ehi)
                    r, ns, nt, sec = check(build(dl, dw, e).prism(), PROPS)
                    rows.append((dl, dw, e, r))
                    print(f"{str(dl):9} {str(dw):9} {str(e):9} "
                          f"{r['spec']:.0f}    {r['haz']:.0f}    "
                          f"{r['live']:.0f}     {ns:<7} {nt:<7} {sec:.2f}")
    # the bound: smallest e_lo with no violation, per (dl, dw), at e_hi=e_lo+3
    print("\nbreak bound (skewed env, e_hi = e_lo+3):")
    for dl in [(1, 1), (1, 3)]:
        for dw in [(1, 1), (1, 3), (2, 4)]:
            ok = [e[0] for (a, b, e, r) in rows
                  if a == dl and b == dw and e[1] == e[0] + 3
                  and r["spec"] == 0 and r["haz"] == 0]
            print(f"  dl={dl} dw={dw}: safe iff e_lo >= {min(ok) if ok else '>5'}"
                  f"   (dw_hi={dw[1]}, dl_hi-dl_lo={dl[1]-dl[0]})")
    print(f"total {time.time()-t_all:.1f} s")
