#!/usr/bin/env python3
"""channel_fit.py -- which delay channel does the research GLS's LUT implement?

Drives one SLICE_LUTX (the research GLS model, cells/gls/prims.v on
origin/claude/research) with random edge traces on its input(s), runs iverilog,
and compares the output event list against three candidate channels:

  transport  out(t) = f(t - d)                     (formal Core/Delay/Pure, lo=hi=d)
  inertial   Lean Filt / InertialRD d d: an edge survives iff the function
             holds its new value for >= d                 (Core/Delay/Inertial)
  saf        "sample at fire": every change of the LUT function at time t
             schedules an update at t + d(pin, edge); the update copies the
             function's value AT FIRE TIME.  Nothing is cancelled.

Usage:  python3 channel_fit.py PRIMS_V [N_TRACES] [--rf RISE FALL] [--pins 2]
PRIMS_V is a copy of prims.v (never read from cells/ in place).
With --rf the LUT is a SLICE_LUTX copy whose A1 path has (rise, fall) delays.
With --pins 2 the LUT is XOR(A1,A2) with per-pin delays 100 / 150 ps.
Exit status 0; prints a score table.
"""
import os, random, subprocess, sys, tempfile

def run_iverilog(prims, tb, workdir):
    tbf = os.path.join(workdir, "tb.v")
    open(tbf, "w").write(tb)
    vvp = os.path.join(workdir, "tb.vvp")
    subprocess.run(["iverilog", "-gspecify", "-o", vvp, tbf, prims], check=True)
    out = subprocess.run(["vvp", "-n", vvp], check=True, capture_output=True, text=True).stdout
    ev = []
    for l in out.splitlines():
        t = l.split()
        if t and t[0] == "O":
            ev.append((int(t[1]), t[2]))
    return ev

RF_MOD = """
module LUT_RF2 (input wire A1, A2, A3, A4, A5, A6, output wire O5, O6);
    parameter [63:0] INIT = 64'h0;
    parameter TR = 56, TF = 124;
    assign O6 = INIT[{A6, A5, A4, A3, A2, A1}];
    assign O5 = 1'bx;
    specify (A1 => O6) = (TR, TF); endspecify
endmodule
"""

def make_tb(edges, pins, rf):
    # edges: list of (time, pin, value), time strictly increasing
    lines = ["`timescale 1ps/1ps", "module tb;", "reg a1 = 0, a2 = 0; wire o;"]
    if rf:
        lines.append("LUT_RF2 #(.INIT(64'hAAAA_AAAA_AAAA_AAAA), .TR(%d), .TF(%d)) u(.A1(a1),.A2(1'b0),.A3(1'b0),.A4(1'b0),.A5(1'b0),.A6(1'b0),.O6(o),.O5());" % rf)
    elif pins == 2:
        lines.append("SLICE_LUTX #(.INIT(64'h6666_6666_6666_6666), .TA1O6(100), .TA2O6(150)) u(.A1(a1),.A2(a2),.A3(1'b0),.A4(1'b0),.A5(1'b0),.A6(1'b0),.O6(o),.O5());")
    else:
        lines.append("SLICE_LUTX #(.INIT(64'hAAAA_AAAA_AAAA_AAAA)) u(.A1(a1),.A2(1'b0),.A3(1'b0),.A4(1'b0),.A5(1'b0),.A6(1'b0),.O6(o),.O5());")
    lines.append("always @(o) if ($time > 500) $display(\"O %0d %b\", $time, o);")
    lines.append("initial begin")
    now = 0
    for t, p, v in edges:
        lines.append("  #%d a%d = %d;" % (t - now, p, v))
        now = t
    lines.append("  #3000 $finish; end")
    lines.append("endmodule")
    if rf:
        lines.append(RF_MOD)
    return "\n".join(lines)

def fn_trace(edges, pins):
    """the LUT function's change list [(t, value, pin)] (zero-time mux tree)."""
    a = {1: 0, 2: 0}
    f = 0
    out = []
    for t, p, v in edges:
        a[p] = v
        nf = a[1] if pins == 1 else a[1] ^ a[2]
        if nf != f:
            out.append((t, nf, p))
            f = nf
    return out

def delay(p, new, old, pins, rf):
    if rf:
        return rf[0] if new == 1 else rf[1]
    if pins == 2:
        return 100 if p == 1 else 150
    return 124

def model_transport(ft, pins, rf):
    ev = []
    for t, v, p in ft:
        ev.append((t + delay(p, v, 1 - v, pins, rf), v))
    ev.sort()
    cur, res = 0, []
    for t, v in ev:
        if v != cur:
            res.append((t, v)); cur = v
    return res

def model_inertial(ft, pins, rf):
    # event-queue inertial: a pending change is cancelled by a later function
    # change scheduled before it matures (ties: a change at exactly t+d does
    # not cancel).  Single delay per change.
    res, cur, pend = [], 0, None
    for t, v, p in ft:
        if pend and pend[0] <= t:
            if pend[1] != cur:
                res.append(pend); cur = pend[1]
            pend = None
        pend = (t + delay(p, v, cur, pins, rf), v) if v != cur else None
    if pend and pend[1] != cur:
        res.append(pend)
    return res

def model_saf(ft, pins, rf):
    fires = sorted(t + delay(p, v, 1 - v, pins, rf) for t, v, p in ft)
    def fval(u):  # function value at time u, an input edge AT u not yet seen
        val = 0
        for t, v, p in ft:
            if t < u:
                val = v
        return val
    res, cur = [], 0
    for u in fires:
        v = fval(u)
        if v != cur:
            res.append((u, v)); cur = v
    return res

def main():
    prims = sys.argv[1]
    n = int(sys.argv[2]) if len(sys.argv) > 2 and not sys.argv[2].startswith("--") else 40
    rf = None
    pins = 1
    if "--rf" in sys.argv:
        i = sys.argv.index("--rf"); rf = (int(sys.argv[i + 1]), int(sys.argv[i + 2]))
    if "--pins" in sys.argv:
        pins = int(sys.argv[sys.argv.index("--pins") + 1])
    rng = random.Random(7)
    score = {"transport": 0, "inertial": 0, "saf": 0}
    first_bad = {}
    with tempfile.TemporaryDirectory() as wd:
        for k in range(n):
            t, edges, a = 1000, [], {1: 0, 2: 0}
            for _ in range(rng.randint(3, 12)):
                t += rng.choice([rng.randint(1, 60), rng.randint(1, 200), rng.randint(100, 400)])
                p = rng.randint(1, pins)
                a[p] ^= 1
                edges.append((t, p, a[p]))
            got = [(tt, 1 if v == "1" else 0) for tt, v in run_iverilog(prims, make_tb(edges, pins, rf), wd)]
            ft = fn_trace(edges, pins)
            for name, m in (("transport", model_transport), ("inertial", model_inertial), ("saf", model_saf)):
                if m(ft, pins, rf) == got:
                    score[name] += 1
                elif name not in first_bad:
                    first_bad[name] = (edges, got, m(ft, pins, rf))
    cfg = "rf=%s" % (rf,) if rf else "pins=%d" % pins
    print("config %s: %d random traces; exact output-event matches:" % (cfg, n))
    for k2, v in score.items():
        print("  %-9s %d/%d" % (k2, v, n))
    for name, (e, g, m) in first_bad.items():
        print("first mismatch for %s:\n  input %s\n  gls   %s\n  model %s" % (name, e, g, m))

if __name__ == "__main__":
    main()
