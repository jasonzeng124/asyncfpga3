#!/usr/bin/env python3
"""Synthesise every cell on its own and check it costs what the review says.

The design review states a LUT count for each cell, and every one of those
numbers rests on the same claim: that two five-input functions sharing at most
five distinct pins land in ONE fractured LUT6_2 rather than two LUT6s.  That
claim is a property of the toolchain, not of the source, so it has to be
measured.  This is the measurement.

What it does and does not prove:

  it DOES prove that yosys keeps every feedback loop, does not duplicate a
  fractured pair into two sites, and emits the cell count the review budgets;

  it does NOT prove the design places and routes -- that is flow.sh, which
  runs one combined top through nextpnr-xilinx and needs the split_lut6_2
  packer patch to survive at all;

  it does NOT prove anything about timing.  Nothing here does.

A LUT6_2 is ONE physical LUT site, so it counts as one.  That is the whole
point of the number being what it is.
"""

import os, re, subprocess, sys, tempfile, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
TC   = pathlib.Path(os.environ.get("TC", "/home/jayjay/dev2/lib/fpgatoolchain"))
YOSYS = TC / "openxc7/bin/yosys"
CELLS_SIM = TC / "openxc7/share/yosys/xilinx/cells_sim.v"

# name -> (expected LUT sites, port list, instantiation, where the review says so)
#
# Costs quoted from the design review's packing table and the per-cell cost
# tables.  Where a cell takes a matched delay the depth is pinned to 4 so the
# delay's own links are a known constant and the rest of the number is the
# cell.
CASES = [
    # ---- C-elements: fan-in four is the ceiling, feedback and rst take two pins
    ("bd_c2",   1, "input rst, input a, input b, output q",
     "bd_c2 u (.a(a), .b(b), .rst(rst), .q(q));"),
    ("bd_c3",   1, "input rst, input a, input b, input c, output q",
     "bd_c3 u (.a(a), .b(b), .c(c), .rst(rst), .q(q));"),
    ("bd_c4",   1, "input rst, input a, input b, input c, input d, output q",
     "bd_c4 u (.a(a), .b(b), .c(c), .d(d), .rst(rst), .q(q));"),
    # Two unrelated C-elements: seven distinct pins, so they must NOT share.
    ("two_c2",  2, "input rst, input a1, input b1, input a2, input b2, output q1, output q2",
     "bd_c2 u1 (.a(a1), .b(b1), .rst(rst), .q(q1));\n"
     "    bd_c2 u2 (.a(a2), .b(b2), .rst(rst), .q(q2));"),
    # Fan-in four in one LUT; five needs a tree, which is two.
    ("ctree4",  1, "input rst, input [3:0] a, output q",
     "bd_ctree #(.N(4)) u (.a(a), .rst(rst), .q(q));"),
    ("ctree5",  2, "input rst, input [4:0] a, output q",
     "bd_ctree #(.N(5)) u (.a(a), .rst(rst), .q(q));"),
    ("ctree8",  3, "input rst, input [7:0] a, output q",
     "bd_ctree #(.N(8)) u (.a(a), .rst(rst), .q(q));"),
    ("ctree16", 5, "input rst, input [15:0] a, output q",
     "bd_ctree #(.N(16)) u (.a(a), .rst(rst), .q(q));"),

    # ---- storage: half a LUT per bit plain, a whole one resettable
    ("latch8",  4, "input en, input [7:0] d, output [7:0] q",
     "bd_latch #(.W(8)) u (.d(d), .en(en), .q(q));"),
    ("latch_rst4", 4, "input rst, input en, input [3:0] d, output [3:0] q",
     "bd_latch_rst #(.W(4)) u (.d(d), .en(en), .rst(rst), .q(q));"),
    ("datamux8", 4, "input s, input [7:0] a, input [7:0] b, output [7:0] z",
     "bd_datamux #(.W(8)) u (.a(a), .b(b), .s(s), .z(z));"),
    ("delay4",  4, "input a, output z", "bd_delay #(.N(4)) u (.a(a), .z(z));"),

    # ---- the pipeline: half a LUT of control per stage, half a LUT per bit
    ("link_pair", 1, "input rst, input req_in, input c_next, output ci, output cj",
     "bd_link_pair u (.req_in(req_in), .c_next(c_next), .rst(rst), .ci(ci), .cj(cj));"),
    # one stage: 1 controller + 8/2 latch bits
    ("link8", 5,
     "input rst, input req_in, output ack_in, input [7:0] data_in,"
     " output req_out, input ack_out, output [7:0] data_out",
     "bd_link #(.W(8)) u (.rst(rst), .req_in(req_in), .ack_in(ack_in),"
     " .data_in(data_in), .req_out(req_out), .ack_out(ack_out), .data_out(data_out));"),
    # four stages: 2 controller LUTs + 4*4 latch = 18
    ("pipe8x4", 18,
     "input rst, input req_in, output ack_in, input [7:0] data_in,"
     " output req_out, input ack_out, output [7:0] data_out",
     "bd_pipe #(.W(8), .N(4)) u (.rst(rst), .req_in(req_in), .ack_in(ack_in),"
     " .data_in(data_in), .req_out(req_out), .ack_out(ack_out), .data_out(data_out));"),

    # ---- routing the handshake
    # steer: both requests share one LUT (two distinct pins), plus the ack OR
    ("steer",   2, "input req, input s, output ack, output req0, input ack0,"
                   " output req1, input ack1",
     "bd_steer u (.req(req), .s(s), .ack(ack), .req0(req0), .ack0(ack0),"
     " .req1(req1), .ack1(ack1));"),
    ("fork4",   1, "input rst, input req, output ack, output [3:0] req_out, input [3:0] ack_in",
     "bd_fork #(.N(4)) u (.rst(rst), .req(req), .ack(ack), .req_out(req_out), .ack_in(ack_in));"),
    ("join4",   1, "input rst, input [3:0] req_in, output [3:0] ack_out, output req, input ack",
     "bd_join #(.N(4)) u (.rst(rst), .req_in(req_in), .ack_out(ack_out), .req(req), .ack(ack));"),

    # ---- converters: encoding is one LUT, decoding is one plus the delay
    ("bd2dr",   1, "input req, input d, output ack, output t, output f, input ack_dr",
     "bd_bd2dr u (.req(req), .d(d), .ack(ack), .t(t), .f(f), .ack_dr(ack_dr));"),
    ("dr2bd",   5, "input t, input f, output ack_dr, output req, output d, input ack",
     "bd_dr2bd #(.DELAY(4)) u (.t(t), .f(f), .ack_dr(ack_dr), .req(req), .d(d), .ack(ack));"),
    # The fix is FREE.  The decode C-element and the request OR share one
    # fractured LUT6_2 -- four distinct inputs between them -- so the LUT2 the
    # bare cell spent on the OR is the same LUT the held cell spends on both.
    # Same number as the bare cell above: that is the claim being measured.
    ("dr2bd_held", 5, "input t, input f, output ack_dr, output req, output d, input ack",
     "bd_dr2bd #(.DELAY(4), .HOLD(1)) u (.t(t), .f(f), .ack_dr(ack_dr),"
     " .req(req), .d(d), .ack(ack));"),

    # ---- merge: 1 OR + 4 delay + 2 acks + 1 select + 4 data
    ("merge8", 12,
     "input rst, input x_req, output x_ack, input [7:0] x_data,"
     " input y_req, output y_ack, input [7:0] y_data,"
     " output z_req, input z_ack, output [7:0] z_data",
     "bd_merge #(.W(8), .DELAY(4)) u (.rst(rst),"
     " .x_req(x_req), .x_ack(x_ack), .x_data(x_data),"
     " .y_req(y_req), .y_ack(y_ack), .y_data(y_data),"
     " .z_req(z_req), .z_ack(z_ack), .z_data(z_data));"),

    # ---- mux: 2 joins + 1 OR + 4 delay + 2 acks + 4 data
    ("mux8", 13,
     "input rst, input x_req, output x_ack, input [7:0] x_data,"
     " input y_req, output y_ack, input [7:0] y_data,"
     " input ctl_req, output ctl_ack, input s,"
     " output z_req, input z_ack, output [7:0] z_data",
     "bd_mux #(.W(8), .DELAY(4)) u (.rst(rst),"
     " .x_req(x_req), .x_ack(x_ack), .x_data(x_data),"
     " .y_req(y_req), .y_ack(y_ack), .y_data(y_data),"
     " .ctl_req(ctl_req), .ctl_ack(ctl_ack), .s(s),"
     " .z_req(z_req), .z_ack(z_ack), .z_data(z_data));"),

    # ---- endpoints: an inverter and a wire
    ("src8",    1, "output req, input ack, output [7:0] data",
     "bd_src #(.W(8), .VAL(8'hA5)) u (.req(req), .ack(ack), .data(data));"),
    ("snk8",    0, "input req, output ack, input [7:0] data",
     "bd_snk #(.W(8)) u (.req(req), .ack(ack), .data(data));"),
    # Source straight into sink: the whole graph is one ring oscillator, and
    # the datum never leaves the tie-off.  One LUT, and nothing else survives.
    ("src_snk", 1, "output probe",
     "wire r, a; wire [7:0] d;\n"
     "    bd_src #(.W(8), .VAL(8'h3C)) us (.req(r), .ack(a), .data(d));\n"
     "    bd_snk #(.W(8)) uk (.req(r), .ack(a), .data(d));\n"
     "    assign probe = r;"),

    # ---- arbitration: the state node and R0 share, the grants share, 2 acks
    ("arbcell", 2, "input rst, input r1, input r2, output g1, output g2",
     "bd_arbcell u (.r1(r1), .r2(r2), .rst(rst), .g1(g1), .g2(g2));"),
    ("arbiter", 4,
     "input rst, input r1, output A1, input r2, output A2,"
     " output R0, input A0, output g1, output g2",
     "bd_arbiter u (.rst(rst), .r1(r1), .A1(A1), .r2(r2), .A2(A2),"
     " .R0(R0), .A0(A0), .g1(g1), .g2(g2));"),
    # The ack-hold that used to be an opt-in variant is now the cell itself,
    # so there is no second entry to price: it was always the same four LUTs
    # on the same two sites, differing only in ustate's constant.
]

RTL = sorted(str(p) for p in (ROOT / "rtl").glob("*.v"))

LUT_CELL = re.compile(r"^\s*(\d+)\s+(LUT[1-6](?:_2)?)\s*$")


def synth(name, ports, body):
    """Run yosys on one wrapper; return {cell: count} for LUT primitives."""
    with tempfile.NamedTemporaryFile("w", suffix=".v", delete=False) as fh:
        fh.write("module top(%s);\n    %s\nendmodule\n" % (ports, body))
        wrapper = fh.name
    script = (
        f"read_verilog -lib -specify {CELLS_SIM}\n"
        f"read_verilog {' '.join(RTL)} {wrapper}\n"
        "synth_xilinx -family xc7 -flatten -nodsp -nosrl -nolutram -nobram"
        " -noclkbuf -top top\n"
        "stat\n"
    )
    try:
        r = subprocess.run([str(YOSYS), "-p", script],
                           capture_output=True, text=True)
    finally:
        os.unlink(wrapper)
    if r.returncode != 0:
        return None, (r.stdout + r.stderr)
    # synth_xilinx prints its own statistics before the explicit stat, so both
    # blocks are in the log.  Only the last one is the final netlist.
    lines = r.stdout.splitlines()
    last = max((i for i, l in enumerate(lines) if l.strip() == "=== top ==="),
               default=None)
    if last is None:
        return None, r.stdout
    counts = {}
    for line in lines[last:]:
        m = LUT_CELL.match(line)
        if m:
            counts[m.group(2)] = counts.get(m.group(2), 0) + int(m.group(1))
    return counts, r.stdout


def main():
    if not YOSYS.exists():
        print(f"yosys not found at {YOSYS}; set TC=", file=sys.stderr)
        return 2

    only = sys.argv[1:]
    bad = 0
    print(f"{'cell':<16}{'expected':>9}{'got':>6}   breakdown")
    print("-" * 68)
    for name, want, ports, body in CASES:
        if only and name not in only:
            continue
        counts, log = synth(name, ports, body)
        if counts is None:
            print(f"{name:<16}{want:>9}{'ERR':>6}   synthesis failed")
            print(log[-1500:])
            bad += 1
            continue
        got = sum(counts.values())
        brk = " ".join(f"{k}x{v}" for k, v in sorted(counts.items()))
        flag = "" if got == want else "   <-- MISMATCH"
        if got != want:
            bad += 1
        print(f"{name:<16}{want:>9}{got:>6}   {brk}{flag}")

    print("-" * 68)
    if bad:
        print(f"{bad} cell(s) do not cost what the design review says")
    else:
        print("every cell costs exactly what the design review says")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
