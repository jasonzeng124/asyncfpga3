"""arb.py -- bd_arbiter (cells/rtl/bd_arb.v, as shipped: held state node) as
dense-time timed automata, checked by TChecker (zones).  Port of C-12b's
formal/tools/async/arb.py; same nodes, monitors and environment, but time unit
1 ps and dense clocks.

  rst      reset release, starts 1, falls in [0, 8] ps
  q, R0    ustate LUT6_2 O6/O5, INIT 64'hFFF0_FFB2_ACAC_ACAC (held, shipped)
           or the UNHELD node (O6 half = bd_c2n_set's FFB2_FFB2),
           pins I0=r1 I1=r2 I2=qs I3=rst I4=A0s I5=1
  qs, qg   routed q at ustate.I2 / ugrant.I2 (wire [lo,hi])
  A0s      routed A0 at ustate.I4 (wire [lo,hi]); ua1/ua2 read A0 directly
  g1, g2   ugrant O5/O6, INIT 64'h0C0C_0C0C_A0A0_A0A0, I0=r1 I1=r2 I2=qg I5=1
  A1, A2   bd_c2 INIT 64'h00E8_00E8_00E8_00E8, I0=g I1=A0 I2=own output I3=rst
  A0       server: follows R0 after [s_lo, s_hi]
  r1, r2   clients: after reset r follows !A; rise any time (no deadline),
           fall [c_lo, c_hi] after A rises
LUT arcs: the header's zero-routing trace (verify/probes/arb_handover.v):
O6 rise 56, O6 fall 124, O5 rise 52, O5 fall 28 ps; each arc gets
[nom - spread, nom + spread].
Monitors (one tck-reach run each): mutex (g1&g2), amutex (A1&A2), ho, tx,
reach1/2, and in transport mode ovf and the *_nr variants (no runt on q).

Run:  python3 -I arb.py <section>    (see __main__)
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tckmodel import Circuit, lut, V, NOT, AND, OR, C, ITE, reach  # noqa

INIT_STATE_HELD = 0xFFF0_FFB2_ACAC_ACAC
INIT_STATE_UNHELD = 0xFFB2_FFB2_ACAC_ACAC
INIT_GRANT = 0x0C0C_0C0C_A0A0_A0A0
INIT_C2 = 0x00E8_00E8_00E8_00E8

O6R, O6F, O5R, O5F = 56, 124, 52, 28     # ps


def iv(nom, spread):
    return (max(nom - spread, 0), nom + spread)


def build(held=True, spread=0, wq_s=(0, 0), wq_g=(0, 0), wa=(0, 0),
          srv=(160, 180), cli=(4, 24), mode="inertial", K=3, u=1):
    """all delays in ps; u = model units per ps (u=10: 0.1 ps resolution;
    zone graphs do not grow with u)."""
    tp = dict(mode=mode, K=K)

    def S(x):
        return (round(x[0] * u), None if x[1] is None else round(x[1] * u))

    wq_s, wq_g, wa, srv, cli = S(wq_s), S(wq_g), S(wa), S(srv), S(cli)

    def iv(nom, spread):
        return S((max(nom - spread, 0), nom + spread))
    c = Circuit()
    for f in ("bad_ho", "bad_tx", "tok"):
        c.flag(f)
    st = INIT_STATE_HELD if held else INIT_STATE_UNHELD
    pins_s = ["r1", "r2", "qs", "rst", "A0s", "1"]
    pins_g = ["r1", "r2", "qg", None, None, "1"]
    c.add("rst", C(0), True, (0, 0), S((0, 8)))
    c.add("q", lut(st, pins_s, "O6"), False, iv(O6R, spread), iv(O6F, spread),
          **tp)
    c.add("R0", lut(st, pins_s, "O5"), False, iv(O5R, spread),
          iv(O5F, spread), **tp)
    c.add("qs", V("q"), False, wq_s, wq_s, **tp)
    c.add("qg", V("q"), False, wq_g, wq_g, **tp)
    c.add("A0s", V("A0"), False, wa, wa, **tp)
    ho = lambda g: AND(NOT(V(g)), V("A0"), NOT(V("tok")))  # noqa: E731
    c.add("g1", lut(INIT_GRANT, pins_g, "O5"), False,
          iv(O5R, spread), iv(O5F, spread), **tp, on_fire=[("bad_ho", ho("g1"))])
    c.add("g2", lut(INIT_GRANT, pins_g, "O6"), False,
          iv(O6R, spread), iv(O6F, spread), **tp, on_fire=[("bad_ho", ho("g2"))])
    for i in (1, 2):
        a = f"A{i}"
        c.add(a, lut(INIT_C2, [f"g{i}", "A0", a, "rst"]), False,
              iv(O6R, spread), iv(O6F, spread), **tp,
              on_fire=[("bad_tx", AND(NOT(V(a)), NOT(V("tok"))))],
              on_fire_set=[("tok", ITE(V(a), V("tok"), C(0)))])
    c.add("A0", V("R0"), False, srv, srv,
          on_fire_set=[("tok", ITE(V("A0"), V("tok"), C(1)))])
    for i in (1, 2):
        c.add(f"r{i}", ITE(V("rst"), V(f"r{i}"), NOT(V(f"A{i}"))), False,
              (0, None), cli)
    return c


TPN = ("q", "R0", "qs", "qg", "A0s", "g1", "g2", "A1", "A2")


def props(mode, which=None):
    p = {"mutex": AND(V("g1"), V("g2")),
         "amutex": AND(V("A1"), V("A2")),
         "ho": V("bad_ho"),
         "tx": V("bad_tx"),
         "reach1": V("A1"),
         "reach2": V("A2")}
    if mode == "transport":
        ovf = OR(*[V(f"ovf_{n}") for n in TPN])
        p["ovf"] = ovf
        nr = NOT(V("mlt_q"))
        p["ovf_nr"] = AND(nr, ovf)
        # no runt at the input of ANY LUT/wire node (no second edge ever
        # queued behind an undelivered one anywhere)
        nra = AND(*[NOT(V(f"mlt_{n}")) for n in TPN])
        for k in ("mutex", "amutex", "ho", "tx"):
            p[k + "_nr"] = AND(nr, p[k])
            p[k + "_nra"] = AND(nra, p[k])
    if which:
        p = {k: p[k] for k in which}
    return p


def row(label, which=None, mem_gb=3.5, timeout=3600, **kw):
    kw.setdefault("mode", "inertial")
    c = build(**kw)
    out = {}
    tot, mx_states, mx_rss = 0.0, 0, 0
    for k, cond in props(kw["mode"], which).items():
        r = reach(c.tck(cond), mem_gb=mem_gb, timeout=timeout)
        if r["reachable"] is None:
            out[k] = "ERR(" + str(r.get("err", ""))[-200:].strip() + ")"
        else:
            out[k] = int(r["reachable"])
        tot += r["seconds"]
        mx_states = max(mx_states, int(r.get("VISITED_STATES", 0)))
        mx_rss = max(mx_rss, int(r.get("MEMORY_MAX_RSS", 0)))
    vals = " ".join(f"{k}={v}" for k, v in out.items())
    print(f"[{kw['mode'][:4]}] {label:44} {vals}  zones<={mx_states} "
          f"rss<={mx_rss//1024}MB {tot:.1f}s", flush=True)
    return out


def sec_basic(mode):
    print(f"== 1. UNHELD grant overlap vs q->ugrant route ({mode}) ==")
    for w in (0, 12, 15, 16, 17, 20, 24):
        row(f"UNHELD wq_g={w} srv=[160,180]", held=False, wq_g=(w, w),
            mode=mode)
    print(f"== 2. server latency (zero routing, {mode}) ==")
    for held in (False, True):
        for s in (4, 40, 56, 60, 80, 160):
            row(f"{'HELD' if held else 'UNHELD'} srv=[{s},{s+20}]",
                held=held, srv=(s, s + 20), mode=mode)
    print(f"== 3. HELD: A0 fork skew ({mode}) ==")
    for w in (0, 32, 64, 96, 112, 116, 128, 192):
        row(f"HELD wa={w} srv=[160,180]", wa=(w, w), mode=mode)


def scan(mode, which, mk, xs, label, **kw):
    """evaluate `which` at each x in xs (ps, may be fractional)."""
    res = {}
    for x in xs:
        res[x] = row(f"{label}={x}", which=which, mode=mode, u=10, **mk(x),
                     **kw)
    for k in which:
        bad = [x for x in res if res[x][k] != 0]
        good = [x for x in res if res[x][k] == 0]
        print(f"   {label}: {k} holds for {label} in "
              f"{[x for x in good]} ; fails at {bad}")


if __name__ == "__main__":
    t0 = time.time()
    what = sys.argv[1] if len(sys.argv) > 1 else "basic"
    mode = sys.argv[2] if len(sys.argv) > 2 else "inertial"
    if what == "dump":
        print(build(mode=mode).tck(V("bad_ho")))
        sys.exit()
    if what == "basic":
        sec_basic(mode)
    elif what == "srv":
        # exact server-latency threshold (s_lo, window s_lo..s_lo+20 ps)
        w = ["amutex", "ho", "tx", "mutex"] if mode == "inertial" else \
            ["amutex_nr", "ho_nr", "tx_nr", "mutex_nr"]
        scan(mode, w, lambda s: dict(srv=(s, s + 20)),
             (55, 55.9, 56, 56.1, 57, 59, 60), "srv_lo")
        scan(mode, ["ho", "tx"] if mode == "inertial" else ["ho_nr", "tx_nr"],
             lambda s: dict(srv=(s, s + 20)), (40, 50, 51.9, 52, 52.1, 53, 56),
             "UNHELD srv_lo", held=False)
    elif what == "wa":
        w = ["amutex", "ho", "tx", "mutex"] if mode == "inertial" else \
            ["amutex_nr", "ho_nr", "tx_nr", "mutex_nr"]
        scan(mode, w, lambda x: dict(wa=(x, x)),
             (112, 115, 115.9, 116, 116.1, 117), "wa")
        scan(mode, ["mutex"] if mode == "inertial" else ["mutex_nr"],
             lambda x: dict(wq_g=(x, x)), (15.9, 16, 16.1, 17),
             "UNHELD wq_g", held=False)
    elif what == "spread":
        # 12b's section 4 (OOM in Storm in transport mode)
        for held in (True, False):
            row(f"{'HELD' if held else 'UNHELD'} spread=8 wq=[0,32] wa=[0,16]",
                held=held, spread=8, wq_g=(0, 32), wq_s=(0, 32), wa=(0, 16),
                srv=(160, 180), mode=mode)
    print(f"total {time.time()-t0:.1f} s")
