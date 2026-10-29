#!/usr/bin/env python3
"""ev8 auditor script: guard ENTRY margin of the gcd_hw arbiter guarded pins, from a routed build.

    python3 entry.py BUILD_DIR [--nomux]   (BUILD_DIR holds gcd_hw_routed.json + gcd_hw.sdf)

Own computation; no formal/ code is imported.  Arc delays come from the auditor's prjxray RC
model audit/tc/xrc.py (routing tree + site pins + OUTMUX), LUT arcs from prjxray slicel/slicem
timing (per physical pin).

Arbiter bd_arbiter (per uarbN):  ua_b = C(grant_b, A0) where A0 = the merge's fork ack (_f g2),
ustate reads A0 and drives ugrant, which drives ua_b's guard pin.  ENTRY (A-events4 ana.py rule):
the A0 event must reach ua_b before the guard reacts to ustate having consumed that same event:

  early path (lo):  A0 -> ustate pin, ustate LUT, ustate -> ugrant pin, ugrant LUT, ugrant -> ua guard pin
  late  path (hi):  A0 -> ua pin
  atomic margin  = lo(early) - hi(late)                        (ua's own LUT cancels: H_ATOMIC_LUT)
  per-pin margin = atomic + lo(ua LUT via guard pin) - hi(ua LUT via A0 pin)

LUT terms are evaluated two ways:  'env' = the cell's [min lo, max hi] envelope over its used
pins (as routed2x.py / the formal bands do), 'pin' = the actual physical-pin IOPATH.
Corners (ps):  slow [SLOW_MIN, SLOW_MAX], fast [FAST_MIN, FAST_MAX], gb [0.668*SLOW_MAX, SLOW_MAX].
"""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tc"))
if "--nomux" in sys.argv:
    os.environ["XRC_NOMUX"] = "1"
import xrc  # noqa: E402

if "--lv2" in sys.argv:
    # prjxray worksheet convention (utils/create_timing_worksheet_db.py, also research xray_delay.py):
    # an LV/LVB long-line node is charged the RC of only two of its (identical) tile wires.
    _orig_rc = xrc.DBx.node_rc

    def _lv2(self, node):
        lv = sorted((t, w) for t, w in node if w.startswith("LV"))
        if not lv:
            return _orig_rc(self, node)
        return _orig_rc(self, frozenset(lv[:2]))
    xrc.DBx.node_rc = _lv2

GB = 0.772 / 1.155


def band(v, corner):
    fmin, fmax, smin, smax = v
    if corner == "slow":
        return smin, smax
    if corner == "fast":
        return fmin, fmax
    if corner == "gb":
        return GB * smax, smax
    raise ValueError(corner)


def main():
    bd = [a for a in sys.argv[1:] if not a.startswith("--")][0]
    R = xrc.Route(bd)
    C = R.cells

    def out_of(cn):
        return "O5" if C[cn]["attributes"]["NEXTPNR_BEL"].endswith("5LUT") else "O6"

    def drv_cell(cn, port):
        bl = C[cn]["connections"].get(port) or [None]
        d = R.driver.get(bl[0])
        return d[0] if d else None

    def pin_from(cn, src):
        ps = [p for p in C[cn]["connections"] if re.fullmatch(r"A[1-6]", p) and drv_cell(cn, p) == src]
        return ps[0] if len(ps) == 1 else None

    def lut(cn, port):
        return R.lut_arc(cn, port, out_of(cn))

    def env(cn):
        vs = [lut(cn, p) for p in C[cn]["connections"] if re.fullmatch(r"A[1-6]", p) and drv_cell(cn, p)]
        vs = [v for v in vs if v]
        return [min(v[0] for v in vs), max(v[1] for v in vs), min(v[2] for v in vs), max(v[3] for v in vs)]

    def wire(src, dst, port):
        n, s = R.sink_of_cellpin(dst, port)
        if s is None:
            raise RuntimeError(f"no routed sink {src} -> {dst}/{port}")
        return s["d"]

    rows = []
    for cn in sorted(C):
        m = re.fullmatch(r"(.*\.uarb\d+)\.ua([12])\.u", cn)
        if not m:
            continue
        base = m.group(1)
        st = base + ".ustate$LUT6"
        if st not in C:
            continue
        ins = {p: drv_cell(cn, p) for p in C[cn]["connections"] if re.fullmatch(r"A[1-6]", p)}
        g = [d for d in ins.values() if d and d.startswith(base + ".ugrant")]
        a0 = [d for d in ins.values() if d and "_f.u.genblk1" in d]
        if len(g) != 1 or len(a0) != 1:
            continue
        g, a0 = g[0], a0[0]
        p_late = pin_from(cn, a0)      # A0 -> ua
        p_guard = pin_from(cn, g)      # ugrant -> ua
        p_st = pin_from(st, a0)        # A0 -> ustate
        p_gs = pin_from(g, st)         # ustate -> ugrant
        if None in (p_late, p_guard, p_st, p_gs):
            continue
        W = dict(a0_ua=wire(a0, cn, p_late), a0_st=wire(a0, st, p_st), st_g=wire(st, g, p_gs), g_ua=wire(g, cn, p_guard))
        L = dict(st_pin=lut(st, p_st), g_pin=lut(g, p_gs), ua_late=lut(cn, p_late), ua_guard=lut(cn, p_guard),
                 st_env=env(st), g_env=env(g), ua_env=env(cn))
        for corner in ("slow", "fast", "gb"):
            lo = lambda v: band(v, corner)[0]
            hi = lambda v: band(v, corner)[1]
            wires_early = lo(W["a0_st"]) + lo(W["st_g"]) + lo(W["g_ua"])
            late = hi(W["a0_ua"])
            r = dict(pin=cn, corner=corner, a0=a0, guard=g, late_pin=p_late, guard_pin=p_guard)
            for mode in ("env", "pin"):
                fst = lo(L["st_env"]) if mode == "env" else lo(L["st_pin"])
                fg = lo(L["g_env"]) if mode == "env" else lo(L["g_pin"])
                atomic = wires_early + fst + fg - late
                uag = lo(L["ua_env"]) if mode == "env" else lo(L["ua_guard"])
                ual = hi(L["ua_env"]) if mode == "env" else hi(L["ua_late"])
                r[f"atomic_{mode}"] = atomic
                r[f"perpin_{mode}"] = atomic + uag - ual
            r["wires"] = {k: [round(x) for x in band(v, corner)] for k, v in W.items()}
            rows.append(r)
    print("# ENTRY margins (ps) of arbiter guarded pins; " + ("XRC_NOMUX" if os.environ.get("XRC_NOMUX") else "with OUTMUX") + (", LV nodes 2 wires" if "--lv2" in sys.argv else ", LV nodes all wires"))
    print("# corner pin | atomic_env perpin_env | atomic_pin perpin_pin | wires lo/hi: A0->ua A0->ustate ustate->ugrant ugrant->ua")
    for r in rows:
        w = r["wires"]
        print(f"{r['corner']:4s} {r['pin'].replace('urig.udut.', ''):34s} pin {r['late_pin']}/{r['guard_pin']} | "
              f"{r['atomic_env']:7.0f} {r['perpin_env']:7.0f} | {r['atomic_pin']:7.0f} {r['perpin_pin']:7.0f} | "
              f"{w['a0_ua']} {w['a0_st']} {w['st_g']} {w['g_ua']}")
    for corner in ("slow", "fast", "gb"):
        rr = [r for r in rows if r["corner"] == corner]
        for k in ("atomic_env", "perpin_env", "atomic_pin", "perpin_pin"):
            mn = min(rr, key=lambda r: r[k])
            neg = sorted((round(r[k]), r["pin"].replace("urig.udut.", "")) for r in rr if r[k] <= 0)
            print(f"SUMMARY {corner} {k}: n={len(rr)} min {mn[k]:.0f} at {mn['pin'].replace('urig.udut.', '')}; <=0: {neg}")


if __name__ == "__main__":
    main()
