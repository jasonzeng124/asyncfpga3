#!/usr/bin/env python3
"""dyn_vsim.py VDIR KERNEL EST_OUT [--mutate N] -- simulate Dynamatic's exported Verilog (research/tools/suite/
dyn_export.py) with iverilog on the calls research/tools/suite/dynamatic_est.py ran, and compare every call's result
and cycle count with the estimator's.

EST_OUT is dynamatic_est.py's output for the kernel ("call a=0x.. b=0x..  cycles N  result R  C R  ok" lines; the
estimator already compiled the C and checked each result against it, so a call counts here only if the estimator's
line says ok). The testbench drives the kernel the way dynamatic_est.py's environment does: every argument channel
and the start token valid from the first cycle after reset, each held until it is taken; every output's ready high;
cycles per call = the cycle in which the last output is taken, counted from 1. A result that differs, or a cycle count
that differs, is printed; exit 1 if any does.

Scalar kernels only (a top port that is not a plain channel or control stops it). --mutate N is the negative control:
the N-th generated cmpi / constant module is altered (a comparison inverted, a constant's lowest bit flipped) in a
copy of VDIR before simulating, so a correct checker must report differences."""
import os
import re
import shutil
import subprocess
import sys
import tempfile



def main():
    vdir, k, est = sys.argv[1], sys.argv[2], sys.argv[3]
    mut = int(sys.argv[sys.argv.index("--mutate") + 1]) if "--mutate" in sys.argv else None
    opt = lambda f: sys.argv[sys.argv.index(f) + 1] if f in sys.argv else None
    buf, vec = opt("--buffered"), opt("--vectors")
    top = open(os.path.join(vdir, k + ".v")).read()
    hdr = top[top.index("(") + 1:top.index(");")]
    # channels: data ports seen above; control channels have only _valid / _ready
    names = re.findall(r"^\s*(?:input|output)\s*(?:\[\d+:0\])?\s*(\w+)_valid", hdr, re.M)
    dirs = dict((n, d) for d, n in re.findall(r"^\s*(input|output)\s*(?:\[\d+:0\])?\s*(\w+)_valid", hdr, re.M))
    widths = {n: int(h) + 1 for h, n in re.findall(r"^\s*(?:input|output)\s*\[(\d+):0\]\s*(\w+)\s*,?\s*$", hdr, re.M)}
    chin = [n for n in names if dirs[n] == "input"]
    chout = [n for n in names if dirs[n] == "output"]
    calls = []
    for ln in open(est):
        m = re.match(r"\s*call\s+(.*?)\s+cycles\s+(\d+)\s+result\s+(\S+)\s+C\s+(\S+)\s+ok\s*$", ln)
        if m:
            args = dict((a, int(v, 0)) for a, v in re.findall(r"(\w+)=(0x[0-9a-fA-F]+|\d+)", m.group(1)))
            calls.append((args, int(m.group(2)), int(m.group(3), 16)))
    if not calls:
        sys.exit("dyn_vsim: no ok call lines in %s" % est)
    data_in = [n for n in chin if n in widths]
    data_out = [n for n in chout if n in widths]
    if len(data_out) > 1:
        sys.exit("dyn_vsim: %d data outputs (%s); this checker takes one" % (len(data_out), data_out))
    # memory kernels: every memref's port (X_loadData in; X_loadEn / X_loadAddr / X_storeEn / X_storeAddr / X_storeData
    # out) gets a BRAM with a one-cycle read, as research/tools/suite/dyn_memcosim.py checked Dynamatic's memory units
    # against; each call's arrays come from the v2 vector file and the expected arrays from the suite's own oracle
    # (dynamatic_est.read_v2 / oracle_mem: the C), read back after the call and compared element by element.
    mems = re.findall(r"^\s*input\s*(?:\[\d+:0\])?\s*(\w+)_loadData\s*,?\s*$", hdr, re.M)
    memcalls, memexp, memgeo = None, None, {}
    if mems:
        if not (buf and vec):
            sys.exit("dyn_vsim: %s has memories %s: needs --buffered BUF.mlir --vectors V2.hex" % (k, mems))
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import dynamatic_est as de
        cir = de.Circuit(buf)
        geo = {name: w for name, kind, c, w in cir.args if kind == "memref"}
        if set(geo) != set(mems):
            sys.exit("dyn_vsim: memrefs %s in the circuit, memory ports %s in the Verilog" % (sorted(geo), mems))
        memgeo = geo
        v2 = de.read_v2(vec, cir)
        memcalls = [mm for _, mm in v2]
        memexp = de.oracle_mem(k, vec, cir)
        if len(v2) != len(calls) or len(memexp) != len(calls):
            sys.exit("dyn_vsim: %d estimator calls, %d v2 calls, %d oracle answers" % (len(calls), len(v2), len(memexp)))
    for a, _, _ in calls:
        miss = [n for n in data_in if n not in a]
        if miss:
            sys.exit("dyn_vsim: the estimator's call has no value for %s" % miss)
    work = tempfile.mkdtemp(prefix="dynvsim_")
    src = vdir
    if mut is not None:
        src = os.path.join(work, "v")
        shutil.copytree(vdir, src)
        gens = sorted(f for f in os.listdir(src) if re.match(r"handshake_(cmpi|constant)_\d+\.v$", f))
        if mut >= len(gens):
            sys.exit("dyn_vsim: --mutate %d: only %d generated modules" % (mut, len(gens)))
        p = os.path.join(src, gens[mut])
        s = open(p).read()
        if "cmpi" in gens[mut]:
            s2 = s.replace("? constant_one : constant_zero", "? constant_zero : constant_one")
        else:
            s2 = re.sub(r"(assign outs\s*=\s*\d+'b[01]*)([01]);", lambda m: m.group(1) + ("1" if m.group(2) == "0" else "0") + ";", s)
        if s2 == s:
            sys.exit("dyn_vsim: --mutate %d: %s not altered" % (mut, gens[mut]))
        open(p, "w").write(s2)
        print("negative control: %s altered" % gens[mut])
    tb = ["`timescale 1ns/1ps", "module tb;", "  reg clk = 0, rst = 1;", "  always #5 clk = ~clk;"]
    for n in chin:
        if n in widths:
            tb.append("  reg [%d:0] %s;" % (widths[n] - 1, n))
        tb.append("  reg %s_valid; wire %s_ready;" % (n, n))
    for n in chout:
        if n in widths:
            tb.append("  wire [%d:0] %s;" % (widths[n] - 1, n))
        tb.append("  wire %s_valid; reg %s_ready;" % (n, n))
    for m in mems:
        size, ew = memgeo[m]
        aw = widths.get(m + "_loadAddr", 1)
        tb.append("  reg [%d:0] mem_%s [0:%d]; reg [%d:0] q_%s = 0;" % (ew - 1, m, size - 1, ew - 1, m))
        tb.append("  wire %s_loadEn, %s_storeEn; wire [%d:0] %s_loadAddr, %s_storeAddr; wire [%d:0] %s_storeData;" % (
            m, m, aw - 1, m, m, ew - 1, m))
        tb.append("  always @(posedge clk) begin if (%s_loadEn) q_%s <= mem_%s[%s_loadAddr]; "
                  "if (%s_storeEn) mem_%s[%s_storeAddr] <= %s_storeData; end" % ((m,) * 8))
    conns = [".clk(clk)", ".rst(rst)"]
    for m in mems:
        conns += [".%s_loadData(q_%s)" % (m, m)] + [".%s_%s(%s_%s)" % (m, x, m, x) for x in
                                                     ("loadEn", "loadAddr", "storeEn", "storeAddr", "storeData")]
    for n in chin + chout:
        if n in widths:
            conns.append(".%s(%s)" % (n, n))
        conns += [".%s_valid(%s_valid)" % (n, n), ".%s_ready(%s_ready)" % (n, n)]
    tb.append("  %s dut (%s);" % (k, ", ".join(conns)))
    tb.append("  integer cyc, last, i; reg [63:0] res; reg %s;" % ", ".join("got_" + n for n in chout))
    tb.append("  task call;")
    tb.append("    input integer cap;")
    for n in data_in:
        tb.append("    input [%d:0] a_%s;" % (widths[n] - 1, n))
    tb.append("    begin")
    tb.append("      rst = 1; %s" % " ".join("%s_valid = 0;" % n for n in chin))
    tb.append("      %s" % " ".join("%s_ready = 1; got_%s = 0;" % (n, n) for n in chout))
    tb.append("      repeat (3) @(posedge clk); #1 rst = 0;")
    tb.append("      %s" % " ".join(("%s = a_%s; " % (n, n) if n in widths else "") + "%s_valid = 1;" % n for n in chin))
    tb.append("      cyc = 0; last = -1;")
    tb.append("      while ((%s) && cyc < cap) begin" % " || ".join("!got_" + n for n in chout))
    tb.append("        @(posedge clk); cyc = cyc + 1;")
    for n in chin:
        tb.append("        if (%s_valid && %s_ready) %s_valid <= 0;" % (n, n, n))
    for n in chout:
        tb.append("        if (%s_valid && %s_ready && !got_%s) begin got_%s = 1; last = cyc;%s end" % (
            n, n, n, n, (" res = %s;" % n) if n in widths else ""))
    tb.append("        #1;")
    tb.append("      end")
    tb.append("      $display(\"CALL cycles %0d result %h\", last, res);")
    tb.append("    end")
    tb.append("  endtask")
    tb.append("  initial begin")
    for j, (a, cyc, _) in enumerate(calls):   # each call capped at 4x the estimator's cycles + 200 (past it: -1)
        for m in mems:
            fi = os.path.join(work, "in_%s_%d.hex" % (m, j))
            open(fi, "w").write("".join("%x\n" % x for x in memcalls[j][m]))
            tb.append('    $readmemh("%s", mem_%s);' % (fi, m))
        tb.append("    call(%s);" % ", ".join(["%d" % (4 * cyc + 200)] + ["%d'h%x" % (widths[n], a[n] & ((1 << widths[n]) - 1)) for n in data_in]))
        for m in mems:
            tb.append('    $writememh("%s", mem_%s);' % (os.path.join(work, "out_%s_%d.hex" % (m, j)), m))
    tb.append("    $finish;")
    tb.append("  end")
    tb.append("endmodule")
    tbp = os.path.join(work, "tb.v")
    open(tbp, "w").write("\n".join(tb) + "\n")
    vs = [os.path.join(src, f) for f in sorted(os.listdir(src)) if f.endswith(".v")]
    exe = os.path.join(work, "sim")
    r = subprocess.run(["iverilog", "-g2012", "-o", exe, "-s", "tb", tbp] + vs, capture_output=True, text=True)
    if r.returncode:
        sys.exit("dyn_vsim: iverilog failed:\n" + r.stderr[-2000:])
    r = subprocess.run(["vvp", "-n", exe], capture_output=True, text=True)
    got = re.findall(r"CALL cycles (-?\d+) result ([0-9a-fx]+)", r.stdout)
    if len(got) != len(calls):
        sys.exit("dyn_vsim: %d calls simulated, %d expected\n%s" % (len(got), len(calls), r.stdout[-1500:]))
    bad = 0
    wout = min(widths[data_out[0]], 32 if mems else 64) if data_out else 0
    for j, ((a, cyc, res), (gc, gr)) in enumerate(zip(calls, got)):
        gr_i = int(gr, 16) if "x" not in gr else None
        okr = (not data_out) or (gr_i is not None and gr_i & ((1 << wout) - 1) == res & ((1 << wout) - 1))
        okc = int(gc) == cyc
        okm, why = True, ""
        for m in mems:
            size, ew = memgeo[m]
            exp_m = memexp[j][1].get(m)
            if exp_m is None:
                continue
            outv = [l.strip() for l in open(os.path.join(work, "out_%s_%d.hex" % (m, j))) if l.strip() and not l.startswith("//")]
            gotm = [int(x, 16) if "x" not in x.lower() else None for x in outv][:len(exp_m)]
            if gotm != [x & ((1 << ew) - 1) for x in exp_m]:
                okm, why = False, why + " array %s differs" % m
        if not (okr and okc and okm):
            bad += 1
        print("  %-40s est cycles %6d result %08x | verilog cycles %6s result %s %s%s" % (
            " ".join("%s=%#x" % kv for kv in a.items()), cyc, res, gc, gr,
            "ok" if okr and okc and okm else ("RESULT DIFFERS" if not okr else ("CYCLES DIFFER" if not okc else "")), why))
    print("dyn_vsim %s: %d calls, %d differ (results%s and cycles against dynamatic_est.py, which checked results "
          "against the C)" % (k, len(calls), bad, ", arrays (the C's)" if mems else ""))
    shutil.rmtree(work, ignore_errors=True)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
