#!/usr/bin/env python3
"""gen_qqmon.py -- UNTRUSTED (lead, 2026-10-31; window corrected after audit P15a): monitor for QQuiet
(Events9ArbB1.QQuiet / the after-S form) on the research routed GLS of gcd_hw.
    python3 -I gen_qqmon.py GLS_WORK > qqmon.v
For every *.ustate$LUT6 cell: its own-feedback pin (ICBUF from the cell's output), loop delay W = ICBUF D + TA_fb,
and for every other pin k with TA_k: Lean's read X u sees pin k at u - TA_k, so QQuiet after an output change at
tau requires no change of pin k at times in (tau - TA_k, tau + W - TA_k]. The monitor flags
    QQ_VIOL <t> <name> A<k> post <dt>   a pin change at t with tau < t <= tau + W - TA_k (dt = t - tau)
    QQ_VIOL <t> <name> A<k> pre <dt>    an output change at t = tau with the pin's last change in (tau - TA_k, tau]
W is this behaviour's own loop delay (what QClean needs for these fixed delays), not the Lean band hi phi(PqQ).
WSCALE=k multiplies W (weak negative control). CONTROL=1 also monitors the feedback pin itself (tag QQ_CTRL):
its change lands exactly at the end of the window (tau + D_icbuf = tau + W - TA_fb), so a working monitor flags
one QQ_CTRL per output change: a near-threshold detection control (audit P15a)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lutnet import load
nm, icbuf, cells, drv = load(sys.argv[1])
sc = int(os.environ.get("WSCALE", "1"))
out = ["module qqmon;"]
for name, c in sorted(nm.items(), key=lambda kv: kv[0]):
    if not name.endswith("ustate$LUT6") or ".uarb" not in name: continue
    v = cells[c]; o = v["out"]; op = v["op"]
    fb = [k for k, w in v["pins"].items() if w in icbuf and icbuf[w][0] == o]
    if len(fb) != 1: print(f"// {name}: feedback pins {fb}", file=sys.stderr); continue
    k = fb[0]; W = (icbuf[v["pins"][k]][1] + v["ta"].get(int(k[1]), 0)) * sc
    tag = name.split("udut.")[-1]
    out.append(f"  // {name}: cell {c} ({op}), feedback pin {k}, loop W = {W} ps")
    out.append(f"  realtime lf_{c} = -1.0e9;")
    others = [p for p, w in v["pins"].items() if p != k and not w.startswith("1'b")]
    if os.environ.get("CONTROL") == "1":
        tak = v["ta"].get(int(k[1]), 0)
        out.append(f"  always @(tb_run.dut.{v['pins'][k]}) if ($realtime > lf_{c} && $realtime - lf_{c} <= {W - tak}) $display(\"QQ_CTRL %0t {tag} {k} %0t\", $realtime, $realtime - lf_{c});")
    for p in others:
        out.append(f"  realtime lp_{c}_{p} = -1.0e9;")
    chk = " ".join(f"if ($realtime - lp_{c}_{p} < {v['ta'].get(int(p[1]), 0)}) $display(\"QQ_VIOL %0t {tag} {p} pre %0t\", $realtime, $realtime - lp_{c}_{p});" for p in others)
    out.append(f"  always @(tb_run.dut.{c}.{op}) begin lf_{c} = $realtime; $display(\"QQ_FLIP %0t {tag}\", $realtime); {chk} end")
    for p in others:
        ta = v["ta"].get(int(p[1]), 0)
        out.append(f"  always @(tb_run.dut.{v['pins'][p]}) begin lp_{c}_{p} = $realtime; "
                   f"if ($realtime > lf_{c} && $realtime - lf_{c} <= {W - ta}) $display(\"QQ_VIOL %0t {tag} {p} post %0t\", $realtime, $realtime - lf_{c}); end")
out.append("endmodule")
print("\n".join(out))
