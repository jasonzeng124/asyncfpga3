#!/usr/bin/env python3
"""gen_qqmon.py -- UNTRUSTED (lead, 2026-10-31): emit qqmon.v, a monitor for QQuiet
(Events9ArbB1.qclean_of_arb's hypothesis) on the research routed GLS of gcd_hw.

    python3 -I gen_qqmon.py GLS_WORK_DIR > qqmon.v      (then compile with tb_run.v + netlist_baked.v)

For every bd_arbiter state LUT (names.map original name *.ustate$LUT6) it finds, in netlist_baked.v,
the LUT's pins, its own-feedback pin (the pin whose net is an ICBUF from the cell's O6) and that pin's
loop delay W = ICBUF D + the cell's TA<pin>O6. The monitor prints
    QQ_FLIP <t> <name>                    at each O6 change,
    QQ_VIOL <t> <name> A<k> <dt>          when another pin of the cell changes within W after an O6 change
(dt = time since that O6 change), and QQ_SUMMARY at $finish (via a final block in tb's $finish path
is not available, so the summary is printed by the analysis script from the log).
The GLS is the research model (nextpnr SDF delays, SAF/fid LUT channel), not A's band model.
"""
import re, sys, os
W = sys.argv[1]
names = {}
for ln in open(os.path.join(W, "names.map")):
    p = ln.split()
    if len(p) == 2 and p[1].endswith("ustate$LUT6"): names[p[0]] = p[1]
net = open(os.path.join(W, "netlist_baked.v")).read()
icbuf = {}  # out wire -> (in net, D)
for m in re.finditer(r"ICBUF #\(\.D\((\d+)\)\) \S+ \(\.I\((\w+)\), \.O\((\w+)\)\);", net):
    icbuf[m.group(3)] = (m.group(2), int(m.group(1)))
out = ["module qqmon;"]
for c, nm in sorted(names.items()):
    m = re.search(r"SLICE_LUTX #\(([^;]*?)\) " + c + r" \(([^;]*)\);", net)
    if not m: print(f"// {c} {nm}: not found", file=sys.stderr); continue
    params, conns = m.group(1), m.group(2)
    pins = dict(re.findall(r"\.(A\d|O6|O5)\(([^)]*)\)", conns))
    o6 = pins["O6"]
    ta = {int(k): int(v) for k, v in re.findall(r"\.TA(\d)O6\((\d+)\)", params)}
    fb = [k for k, v in pins.items() if k.startswith("A") and v in icbuf and icbuf[v][0] == o6]
    if len(fb) != 1: print(f"// {c} {nm}: feedback pins {fb}", file=sys.stderr); continue
    k = fb[0]; Wd = (icbuf[pins[k]][1] + ta.get(int(k[1]), 0)) * int(os.environ.get("WSCALE", "1"))
    others = [p for p, v in pins.items() if p.startswith("A") and p != k and not v.startswith("1'b")]
    tag = nm.split("udut.")[-1]
    out.append(f"  // {nm}: cell {c}, feedback pin {k}, loop W = {Wd} ps")
    out.append(f"  realtime lf_{c} = -1.0e9;")
    out.append(f"  always @(tb_run.dut.{c}.O6) begin lf_{c} = $realtime; $display(\"QQ_FLIP %0t {tag}\", $realtime); end")
    for p in others:
        out.append(f"  always @(tb_run.dut.{pins[p]}) if ($realtime > lf_{c} && $realtime - lf_{c} <= {Wd}) "
                   f"$display(\"QQ_VIOL %0t {tag} {p} %0t W={Wd}\", $realtime, $realtime - lf_{c});")
out.append("endmodule")
print("\n".join(out))
