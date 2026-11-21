"""celem.py -- bd_c2 (cells/rtl/bd_ce.v, INIT 64'h00E8_00E8_00E8_00E8) as
dense-time timed automata, checked by TChecker (zones).  Port of C-12b's
formal/tools/async/celem.py; same nodes, same environment:

  rst   one-shot reset release: starts 1, falls at some time in [0, R]
  O     LUT6 output: REAL INIT, pins I0=a I1=b I2=qp I3=rst I4=0 I5=0, [dl]
  qp    routed feedback net at pin I2 (buffer of O), [dw]
  a, b  four-phase environment, each toggles [e] after it sees O catch up
Properties (each a separate tck-reach run):
  spec  O fires in a pre-state where NOT (a = b != O)
  haz   O's excitation withdrawn before it fired (inertial only)
  ovf   a transport queue overflowed (transport only; exactness monitor)

Question (C-12c item 1): is "spec holds iff e_lo >= dw_hi" exact in dense
time?  Delays are scaled by SCALE so that e_lo can sit strictly between two
integers of 12b's tick grid (e_lo = dw_hi - 1/SCALE).

Run:  python3 -I celem.py            (prints a table; ~1 min)
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tckmodel import Circuit, lut, V, NOT, AND, EQ, OR, C, reach  # noqa: E402

INIT_C2 = 0x00E8_00E8_00E8_00E8
SCALE = 10


def build(dl, dw, e, R=2, mode="inertial"):
    c = Circuit()
    c.flag("bad_spec")
    c.add("rst", C(0), True, (0, 0), (0, R))
    c.add("O", lut(INIT_C2, ["a", "b", "qp", "rst"]), False, dl, dl,
          watch_hazard=True, mode=mode, K=3,
          on_fire=[("bad_spec",
                    NOT(AND(EQ(V("a"), V("b")), NOT(EQ(V("a"), V("O"))))))])
    c.add("qp", V("O"), False, dw, dw, mode=mode, K=3)
    c.add("a", NOT(V("O")), False, e, e)
    c.add("b", NOT(V("O")), False, e, e)
    return c


def props(mode):
    p = {"spec": V("bad_spec")}
    if mode == "inertial":
        p["haz"] = V("hz_O")
    else:
        p["ovf"] = OR(V("ovf_O"), V("ovf_qp"))
    p["reachO"] = V("O")   # non-vacuity: O can rise
    return p


def sc(iv):
    return (iv[0] * SCALE, iv[1] * SCALE)


def main():
    t_all = time.time()
    print("units: 12b ticks x", SCALE, "(so e_lo steps of 1/%d tick)" % SCALE)
    for mode in ("inertial", "transport"):
        print(f"--- {mode} ---")
        print(f"{'dl':10} {'dw':10} {'e':12} " +
              " ".join(f"{k:6}" for k in props(mode)) + "  sec  maxstates")
        for dl in [(1, 1), (1, 3)]:
            for dw in [(1, 1), (1, 3), (2, 4)]:
                D = dw[1] * SCALE
                for elo in (D - SCALE, D - 1, D, D + 1, D + SCALE):
                    e = (elo, elo + 3 * SCALE)
                    r = {}
                    sec = 0
                    mx = 0
                    for k, cond in props(mode).items():
                        out = reach(build(sc(dl), sc(dw), e, R=2 * SCALE,
                                          mode=mode).tck(cond))
                        r[k] = out["reachable"]
                        if r[k] is None:
                            print("ERR", out.get("err"))
                            sys.exit(1)
                        sec += out["seconds"]
                        mx = max(mx, int(out.get("VISITED_STATES", 0)))
                    print(f"{str(sc(dl)):10} {str(sc(dw)):10} {str(e):12} " +
                          " ".join(f"{int(r[k]):<6}" for k in r) +
                          f"  {sec:.2f} {mx}", flush=True)
    print(f"total {time.time()-t_all:.1f} s")


def thresholds():
    """exact break points: scan e_lo (scaled units) and report the least
    e_lo from which the property holds for every larger e_lo scanned."""
    t_all = time.time()
    print("threshold scan (units = 1/%d of a 12b tick); e = [e_lo, e_lo+30]"
          % SCALE)
    for mode in ("inertial", "transport"):
        keys = ["spec", "haz"] if mode == "inertial" else ["spec", "ovf"]
        print(f"--- {mode} ---")
        for dl in [(10, 10), (10, 30), (5, 5), (20, 20), (20, 30)]:
            for dw in [(10, 10), (10, 30), (20, 40), (5, 25)]:
                res = {}
                for elo in range(0, dw[1] + 3):
                    c = build(dl, dw, (elo, elo + 30), R=20, mode=mode)
                    res[elo] = {k: reach(c.tck(props(mode)[k]))["reachable"]
                                for k in keys}
                line = f"dl={str(dl):9} dw={str(dw):9}"
                for k in keys:
                    bad = [e for e in res if res[e][k]]
                    thr = (max(bad) + 1) if bad else 0
                    mono = all(res[e][k] for e in res if e < thr)
                    line += f"  {k} holds iff e_lo >= {thr:3}" + \
                        ("" if mono else " (NON-MONOTONE)")
                print(line + f"   dw_hi={dw[1]} dw_hi-dl_lo={dw[1]-dl[0]}",
                      flush=True)
    print(f"total {time.time()-t_all:.1f} s")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "thr":
        thresholds()
        sys.exit()
    if len(sys.argv) > 1 and sys.argv[1] == "dump":
        print(build((1, 2), (1, 3), (1, 4),
                    mode=sys.argv[2] if len(sys.argv) > 2 else "inertial")
              .tck(V("bad_spec")))
        sys.exit()
    main()
