#!/usr/bin/env python3
"""Generate a PS7-driven autonomous batch-benchmark top for a compiled bdc
kernel, from the kernel's OWN function signature -- so a new kernel needs no
hand-editing of the bench (item 3 of the harness spec).

WHY THIS EXISTS

hw/gcd_bench.v is a hand-written instance of this shape for gcd specifically:
two hardcoded 32-bit operand registers, a bd_fork #(.N(3)) width baked in by
hand.  That does not generalise to ipow (2 args), collatz/isprime (1 arg) or
collatz64 (1 arg, 64 BITS).  Rather than hand-edit six near-duplicate bench
files -- which is exactly the kind of drift hw/gcd_ps.v's header warns about
("The two files must not drift") -- this script reads the same parsed
handshake.func bdc/emit.py itself reads, and emits the operand register
count, register widths and bd_fork width from func.args, the same way
bdc/emit.py derives its own port list (bdc/emit.py:1417-1429).

FIXED REGISTER LAYOUT, VARIABLE KERNEL

Every one of the six kernels in kernels/ has at most two 32-bit operand
WORDS: two i32 args (gcd, ipow, xorshift) or one i64 arg (collatz64) or one
i32 arg (collatz, isprime).  So rather than a register map whose shape
depends on the kernel, this generator allocates a FIXED two-word operand
file (OPERAND0/OPERAND1) for every kernel and maps the function's actual
argument(s) onto it: two i32 args get one word each; one i64 arg gets its
low/high halves; one i32 arg uses OPERAND0 and leaves OPERAND1 unused.  That
keeps one host script and one xsdb driver valid for all six kernels, and
raises loudly (not silently pads/truncates) if a future kernel needs a
third word -- see MAX_WORDS below.

WHAT DOES vary per kernel, and is computed here from the signature:
  - the bd_fork width (nargs + 1, matching hw/gcd_ps.v:348's #(.N(3)) for
    gcd's 2 args + start)
  - the bd_join width inside the null-kernel control (item: null-kernel
    below)
  - which operand words are wired to which DUT port, and at what width
  - per-kernel DOMAIN RESTRICTIONS on the uniform-random generator, derived
    from actually reading each kernel's C loop bounds (kernels/*.c), not
    guessed:
      * collatz/collatz64: while (n != 1) does not terminate for n <= 0
        (0 stays 0 forever under >>1; negative n cycles under the 3n+1 arm
        -- e.g. n=-1 -> -2 -> -1 -> ...).  A "uniform random" default that
        can permanently wedge the batch FSM is not a benchmark, it is a
        hang, so n is restricted to the kernel's actual domain: positive
        and nonzero.  This is a per-kernel termination requirement, not a
        blanket correction -- gcd, ipow, isprime and xorshift's operands
        get no such mask.
      * xorshift: the outer loop runs exactly `rounds` times with O(1) per
        round, so a full-range 32-bit `rounds` gives one run up to 2^31
        iterations -- finite, but it would dominate a batch and blow the
        "few fat batches" budget for no statistical benefit (the kernel's
        entire behaviour per round is identical; sampling round count
        beyond a few thousand tells you nothing new about the mixing
        function). `rounds` is masked to 12 bits (0-4095).
      * gcd, ipow, isprime: no mask.  gcd short-circuits on a==0/b==0
        (kernels' gcd.c terminates for any 32-bit pair); ipow's loop trip
        count is bounded by e's bit length either way; isprime's outer trial
        loop is bounded by sqrt(n) regardless of sign (n<2 returns
        immediately).

Usage:
    python3 cells/hw/gen_bench.py gcd -o build/gen/gcd_bench_gen.v
    python3 cells/hw/gen_bench.py collatz64 --null -o build/gen/collatz64_null_gen.v --top collatz64_null
"""
import argparse
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "bdc"))
from hs import parse  # noqa: E402

MAX_WORDS = 2  # every kernel in kernels/ needs at most this many 32-bit words

# Per-kernel operand domain restriction: kernel name -> list of one entry per
# data arg, each either None (no restriction) or a dict describing the mask.
# 'positive_nonzero' clears the top bit of the arg's OWN width and remaps an
# all-zero result to 1.  'and_mask' ANDs the low 32 bits of that arg's first
# word with the given constant (used for xorshift's rounds).
DOMAIN_RESTRICTIONS = {
    "collatz":   {"n": {"kind": "positive_nonzero"}},
    "collatz64": {"n": {"kind": "positive_nonzero"}},
    "xorshift":  {"rounds": {"kind": "and_mask", "value": "32'h00000FFF"}},
    # gcd: found by simulation, not guessed -- see gen_bench.py's module
    # header "GCD'S OWN OVERFLOW HANG" note.  kernels/../gcd.c's main loop
    # computes `diff = a - b` and `a = -diff` in plain `int`; for a full
    # 32-bit-uniform (a, b) pair with opposite signs and magnitudes near
    # 2^31, that subtraction/negation silently overflows 32-bit two's
    # complement, and the wraparound breaks the magnitude-decrease invariant
    # Stein's algorithm's termination relies on.  A Python model of the
    # exact int32 arithmetic (not Python's unbounded ints) confirms a real
    # operand pair (a=0xace12345, b=0x59c2468b) enters a permanent state
    # CYCLE after ~20221 iterations -- the algorithm ITSELF does not
    # terminate for that input, so the compiled hardware correctly hangs
    # waiting for a result that was never coming.  This is not a hardware
    # bug and not fixable by padding a delay; it is fixed by keeping both
    # operands in gcd's actual well-defined domain: nonnegative.  With
    # a, b in [0, 2^31-1], `a - b` is representable in int32 without
    # overflow (range [-(2^31-1), 2^31-1]) and `-diff` is too, so the
    # convergence proof holds and the measured 32 kernels/gcd.c a==0/b==0
    # early-return + CTZ-reduction termination argument is valid again.
    "gcd": {"a": {"kind": "nonnegative"}, "b": {"kind": "nonnegative"}},
}


def words_for(width):
    assert width % 32 == 0, f"arg width {width} is not a multiple of 32 -- unsupported"
    return width // 32


def load_signature(kernel, frontend_dir):
    mlir = os.path.join(frontend_dir, kernel, "comp", "handshake_transformed.mlir")
    if not os.path.exists(mlir):
        raise SystemExit(f"no compiled signature for {kernel!r}: {mlir} does not exist "
                          f"(expected build/frontend/{kernel}/comp/handshake_transformed.mlir)")
    funcs = [f for f in parse.parse_module(open(mlir).read(), filename=mlir)
             if not f.is_declaration]
    if len(funcs) != 1:
        raise SystemExit(f"{mlir}: expected exactly one defined handshake.func, found {len(funcs)}")
    func = funcs[0]
    data_args = [a for a in func.args if not a.is_control]
    total_words = sum(words_for(a.width) for a in data_args)
    if total_words > MAX_WORDS:
        raise SystemExit(f"{kernel}: needs {total_words} operand words, this generator's fixed "
                          f"register file only has {MAX_WORDS} -- widen MAX_WORDS and the "
                          f"register map before using this kernel, do not silently truncate it")
    if func.name != kernel:
        raise SystemExit(f"{mlir}: handshake.func @{func.name} does not match kernel name "
                          f"{kernel!r} passed on the command line")
    return data_args


def emit(kernel, is_null, top_name):
    frontend_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "build", "frontend")
    data_args = load_signature(kernel, frontend_dir)
    nargs = len(data_args)
    restr = DOMAIN_RESTRICTIONS.get(kernel, {})

    dut_module = f"bdc_null_{kernel}" if is_null else f"bdc_{kernel}"
    kernel_file_comment = (f"// DUT: {dut_module} -- trivial pass-through, same port shape as bdc_{kernel}"
                            if is_null else f"// DUT: {dut_module}, compiled from kernels/{kernel}")

    lines = []
    P = lines.append

    P(f"// Generated by cells/hw/gen_bench.py for kernel {kernel!r} "
      f"({'NULL control' if is_null else 'real DUT'}).")
    P("// DO NOT EDIT -- regenerate instead: python3 cells/hw/gen_bench.py "
      f"{kernel}{' --null' if is_null else ''} -o <path>")
    P(kernel_file_comment)
    P(f"// {nargs} data arg(s): " + ", ".join(f"{a.name}:i{a.width}" for a in data_args))
    if restr:
        P("// Domain restrictions applied to the uniform-random generator (see gen_bench.py header):")
        for name, rule in restr.items():
            P(f"//   {name}: {rule}")
    P("`default_nettype none")
    P("")

    # -------------------------------------------------------------------
    # null-kernel DUT, generated inline so its port shape is provably
    # identical to the real one -- same arg list, same out0/p_end shape.
    if is_null:
        P(f"// Trivial pass-through control: joins every input channel, XOR-folds")
        P(f"// the operand data down to 32 bits, and produces out0/p_end after a")
        P(f"// short self-timed delay -- so it pays the same fork/join/pulse-adapter")
        P(f"// overhead as {('bdc_' + kernel)} without doing {kernel}'s own work.  This")
        P(f"// is the null-kernel control referenced in the harness spec: subtract its")
        P(f"// latency from {kernel}'s to get the kernel's OWN contribution.")
        ports = ["    input  wire             rst"]
        for a in data_args:
            ports.append(f"    input  wire             {a.name}_req")
            ports.append(f"    output wire             {a.name}_ack")
            ports.append(f"    input  wire [{a.width - 1}:0]{' ' * max(1, 5 - len(str(a.width - 1)))}   {a.name}_data")
        ports.append("    input  wire             start_req")
        ports.append("    output wire             start_ack")
        ports.append("    output wire             out0_req")
        ports.append("    input  wire             out0_ack")
        ports.append("    output wire [31:0]      out0_data")
        ports.append("    output wire             p_end_req")
        ports.append("    input  wire             p_end_ack);")
        P(f"module {dut_module} (")
        P(",\n".join(ports))
        n_join = nargs + 1
        req_list = ", ".join(["start_req"] + [a.name + "_req" for a in reversed(data_args)])
        ack_list = ", ".join(["start_ack"] + [a.name + "_ack" for a in reversed(data_args)])
        P(f"    wire joined_req, joined_ack;")
        P(f"    bd_join #(.N({n_join})) ujoin (.rst(rst), .req_in({{{req_list}}}),")
        P(f"        .ack_out({{{ack_list}}}), .req(joined_req), .ack(joined_ack));")
        P(f"    // N=6/N=10: a genuinely trivial pass-through's own fixed overhead --")
        P(f"    // nothing more. An earlier version of this file padded these to N=80 to")
        P(f"    // work around a hang (see the bridge's i_ack_latched/o_req_latched comment")
        P(f"    // for the real fix and why that padding was wrong): the null control exists")
        P(f"    // to be SUBTRACTED from every real kernel's latency, so inflating its own")
        P(f"    // round trip by ~20 ns silently under-reports every kernel by ~20 ns. The")
        P(f"    // actual defect was in the FSM's POLLER, not in this kernel, and belongs")
        P(f"    // fixed there -- these stay minimal.")
        P(f"    bd_delay #(.N(6)) uack (.a(joined_req), .z(joined_ack));")
        P(f"    bd_delay #(.N(10)) uout (.a(joined_req), .z(out0_req));")
        fold_terms = []
        for a in data_args:
            for w in range(words_for(a.width)):
                fold_terms.append(f"{a.name}_data[{w * 32 + 31}:{w * 32}]")
        P(f"    assign out0_data = {' ^ '.join(fold_terms)};")
        P(f"    assign p_end_req = joined_req;")
        P(f"endmodule")
        P("")

    # -------------------------------------------------------------------
    # bridge module
    bridge = f"{top_name}_bridge"
    P(f"module {bridge} (")
    P("    input         aclk,")
    P("    input         aresetn,")
    P("    input         awvalid, output awready, input [31:0] awaddr, input [11:0] awid,")
    P("    input         wvalid,  output wready,  input [31:0] wdata,  input [3:0] wstrb,")
    P("    output        bvalid,  input  bready,  output [1:0] bresp,  output [11:0] bid,")
    P("    input         arvalid, output arready, input [31:0] araddr, input [11:0] arid,")
    P("    output        rvalid,  input  rready,  output [31:0] rdata,")
    P("    output [1:0]  rresp,   output [11:0] rid,")
    P("    output        core_i_ack,")
    P("    output        core_o_req")
    P(");")
    P("")
    P("    reg        axi_awready, axi_wready, axi_bvalid;")
    P("    reg        axi_arready, axi_rvalid;")
    P("    reg [6:0]  axi_awaddr, axi_araddr;   // word address: 7 bits -> 128 words, room for the 64-bucket histogram")
    P("    reg [11:0] axi_bid, axi_rid;")
    P("    reg        aw_en;")
    P("")
    P("    assign awready = axi_awready;")
    P("    assign wready  = axi_wready;")
    P("    assign bvalid  = axi_bvalid;")
    P("    assign bresp   = 2'b00;")
    P("    assign bid     = axi_bid;")
    P("    assign arready = axi_arready;")
    P("    assign rvalid  = axi_rvalid;")
    P("    assign rresp   = 2'b00;")
    P("    assign rid     = axi_rid;")
    P("")
    P("    wire do_write = axi_awready && awvalid && axi_wready && wvalid;")
    P("")
    P("    reg        ctrl_i_req, ctrl_o_ack, ctrl_rst;")
    P("    reg [31:0] op0, op1;                 // fixed two-word operand file (host-facing)")
    P("    reg [31:0] n_runs, cycles, prep_cycles, lat_min, lat_max;")
    P("    reg        bctrl_start, bctrl_rst;")
    P("    reg [1:0]  bctrl_mode;                // 0=uniform 1=fixed 2=legacy-biased")
    P("    reg [31:0] last_op0, last_op1;")
    P("    reg [31:0] sig;")
    P("    // mismatch_sticky is a FIXED-mode-ONLY repeatability latch (see the")
    P("    // bctrl_mode == 2'd1 guard below): it is unconditionally cleared at every")
    P("    // batch start/reset regardless of mode and is only ever SET inside that")
    P("    // FIXED-mode branch. A UNIFORM-mode (or LEGACY-mode) batch therefore")
    P("    // reads mismatch_sticky==0 ALWAYS, whether or not the kernel's answers")
    P("    // were correct -- it is not an on-chip oracle for those modes, only for")
    P("    // FIXED. Do not read a green MISM_ST from a UNIFORM batch as evidence of")
    P("    // anything; a real UNIFORM-mode SIG mismatch was found this way (n=4,")
    P("    // gcd, see hw/run_gcd_sig_check.sh) with MISM_ST reading 0 throughout.")
    P("    reg        mismatch_sticky;")
    P("    reg [31:0] mismatch_idx, mismatch_val, mismatch_ref;")
    P("")
    P("    reg [1:0]  sync_i_ack, sync_o_req;")
    P("    reg [31:0] o_data_capture;")
    P("")
    P("    wire i_ack_s = sync_i_ack[1];")
    P("    wire o_req_s = sync_o_req[1];")
    P("")
    P("    wire        i_req_pl, o_ack_pl, rst_pl;")
    P("    wire        i_ack_pl, o_req_pl;")
    P("    wire [31:0] o_data_pl;")
    P("")
    P("    assign rst_pl = ctrl_rst;   // bdc kernels reset ACTIVE-HIGH; see hw/gcd_ps.v")
    P("")
    P("    // ---- the batch FSM ------------------------------------------------------")
    P("    localparam S_IDLE = 3'd0, S_PREP = 3'd1, S_ISSUE = 3'd2,")
    P("               S_WAIT_ACK = 3'd3, S_WAIT_RES = 3'd4, S_ACK = 3'd5,")
    P("               S_RTZ = 3'd6, S_NEXT = 3'd7;")
    P("")
    P("    reg [2:0]  st;")
    P("    reg [31:0] runs_done, lat_ctr;")
    P("    reg [31:0] prep_ctr;")
    P("    // run_gap: how many aclk cycles S_PREP occupies before each run is")
    P("    // issued, i.e. the INTER-RUN GAP, programmable at 7'h14 (byte 0x50).")
    P("    // It exists to make ISSUE RATE a runtime variable inside ONE bitstream.")
    P("    //")
    P("    // Why that matters: the compiled kernel has been validated 3014/3014 on")
    P("    // silicon through hw/xsdb_gcd_sweep.tcl, but that harness drives ONE")
    P("    // vector per ~80 ms of JTAG round-trips. This bench drives 64 runs in")
    P("    // ~410 us back-to-back, and that is the regime where batches were seen")
    P("    // to park forever in S_WAIT_RES with o_req_s=0 (run 16, 26, 34, 61 --")
    P("    // a different index every time, on a fixed seed). Rebuilding with a")
    P("    // wider gap would confound the answer, because a rebuild also reroutes")
    P("    // and \"one route is a sample\". Making the gap a REGISTER means the fast")
    P("    // and slow cases run on the SAME bitstream and the SAME route, so a")
    P("    // difference between them is attributable to rate and nothing else.")
    P("    //")
    P("    // Default 15 reproduces the original fixed 4-bit `prep_ctr == 4'd15`")
    P("    // behaviour exactly, so an unwritten register changes nothing.")
    P("    reg [31:0] run_gap;")
    P("    reg        bench_busy, bench_done, bench_set_req, bench_o_ack;")
    P("    reg [31:0] lfsr;")
    P("    wire [31:0] lfsr_n1 = {lfsr[30:0], lfsr[31]^lfsr[21]^lfsr[1]^lfsr[0]};")
    P("    wire [31:0] lfsr_n2 = {lfsr_n1[30:0], lfsr_n1[31]^lfsr_n1[21]^lfsr_n1[1]^lfsr_n1[0]};")
    P("    reg [31:0] bench_op0, bench_op1;")
    P("    reg        start_d;")
    P("    reg        have_ref;                  // FIXED-mode repeatability reference latched")
    P("")
    P("    wire       start_rise = bctrl_start & ~start_d;")
    P("")
    P("    // Bundled-data hazard note (see hw/gcd_bench.v): the FSM must not move")
    P("    // bench_op0/1 while a request is in flight.  S_PREP settles them first.")
    P("    wire [31:0] op0_to_core = bench_busy ? bench_op0 : op0;")
    P("    wire [31:0] op1_to_core = bench_busy ? bench_op1 : op1;")
    P("")
    P("    wire req_clr = i_ack_pl | ~aresetn;")
    P("    reg  req_core = 1'b0;")
    P("    always @(posedge aclk or posedge req_clr) begin")
    P("        if (req_clr)                                            req_core <= 1'b0;")
    P("        else if (bench_busy && bench_set_req)                   req_core <= 1'b1;")
    P("        else if (!bench_busy && do_write && axi_awaddr == 7'h0) req_core <= wdata[0];")
    P("    end")
    P("    assign i_req_pl = req_core;")
    P("")
    P("    wire i_ack_host = ctrl_i_req & ~req_core;")
    P("    assign o_ack_pl = (bench_busy ? bench_o_ack : ctrl_o_ack) & o_req_pl;")
    P("")
    P("    // ---- async-clearing pulse adapter (see hw-docs/02, gcd_ps.v's req_clr) --")
    P("    // The FSM's own S_WAIT_ACK/S_WAIT_RES steps are synchronous pollers: they")
    P("    // can only observe a level that is HIGH AT a clock edge. i_ack_pl/o_req_pl")
    P("    // are raw combinational core wires that can rise and fall entirely between")
    P("    // two clock edges (this is deterministic, not rare, for a trivial/fast")
    P("    // kernel -- it hung the null-kernel control 100% of the time). The fix")
    P("    // belongs in the poller, not in the kernel: latch each pulse in a flop that")
    P("    // is asynchronously SET the instant the wire rises (so no edge is ever")
    P("    // missed regardless of pulse width) and synchronously CLEARED by the FSM")
    P("    // once it has consumed the observation, mirroring req_core's async-CLEAR")
    P("    // shape above but with the opposite polarity.")
    P("    // Priority matters here: CLEAR must win whenever it applies, not just when")
    P("    // the raw wire happens to be low (a version that checked SET before CLEAR")
    P("    // never cleared while the real kernels\' i_ack_pl/o_req_pl held HIGH as a")
    P("    // level across S_ACK/S_RTZ/..., stayed stuck set, and fired one run early --")
    P("    // wrong SIG, a spurious FIXED-mode mismatch, a UNIFORM-mode hang).")
    P("    //")
    P("    // The arm/catch window is the WHOLE in-flight period (S_ISSUE..S_RTZ), not")
    P("    // just the single FSM state that consumes it: the null kernel derives BOTH")
    P("    // i_ack and o_req from the same trivial joined_req at different bd_delay")
    P("    // depths (N=6 vs N=10), so o_req can rise and fall in well under 1 ns --")
    P("    // entirely while st is still S_WAIT_ACK, one full clock edge before the FSM")
    P("    // even reaches S_WAIT_RES to open a narrower window. A version gated on")
    P("    // \"st == S_WAIT_RES\" missed that pulse every time (permanent stall, caught")
    P("    // by tb_null_gcd_gen.v/tb_null_isprime_gen.v) because it wasn\'t listening")
    P("    // yet when the pulse actually happened. Clearing only once, at S_ISSUE (the")
    P("    // one state guaranteed to run exactly once per request, right as the new")
    P("    // request is launched and before anything could have responded), and")
    P("    // otherwise staying async-armed for the rest of the transaction, catches")
    P("    // the pulse regardless of which FSM state happens to be current when it")
    P("    // arrives.")
    P("    // yosys\'s proc pass only synthesizes an async flop off a TWO-edge")
    P("    // sensitivity list (clock + one derived async condition) -- the obvious")
    P("    // three-edge form (posedge aclk or posedge i_ack_pl or negedge aresetn)")
    P("    // simulates fine in iverilog but yosys refused it outright (\"Multiple")
    P("    // edge sensitive events found for this signal!\", caught building the")
    P("    // first bitstream after this fix). req_clr above dodges this the same")
    P("    // way, but ALSO tests the exact sensitivity-list wire as the outermost")
    P("    // condition (\"if (req_clr) ...\") -- yosys\'s async-reset pattern match")
    P("    // requires that literal shape (same identifier, outermost, unconditional)")
    P("    // to recognise it as a single async control at all; a first version here")
    P("    // OR\'d the same way but tested \"if (!aresetn)\" as the outer condition")
    P("    // (a different, only logically-equivalent expression) and hit the exact")
    P("    // same synth error, because yosys never matched it to the sensitivity")
    P("    // wire and fell back to treating it as multi-edge. Testing the event")
    P("    // wire itself outermost, then disambiguating reset-vs-pulse inside,")
    P("    // preserves the same priority (reset > S_ISSUE clear > pulse SET) in a")
    P("    // shape yosys actually recognises.")
    P("    reg i_ack_latched, o_req_latched;")
    P("    wire i_ack_latch_evt = i_ack_pl | ~aresetn;")
    P("    wire o_req_latch_evt = o_req_pl | ~aresetn;")
    P("    always @(posedge aclk or posedge i_ack_latch_evt) begin")
    P("        if (i_ack_latch_evt)     i_ack_latched <= aresetn;         // aresetn low: CLEAR; else: async SET")
    P("        else if (st == S_ISSUE)  i_ack_latched <= 1\'b0;           // clear once, at request launch")
    P("    end")
    P("    always @(posedge aclk or posedge o_req_latch_evt) begin")
    P("        if (o_req_latch_evt)     o_req_latched <= aresetn;")
    P("        else if (st == S_ISSUE)  o_req_latched <= 1\'b0;")
    P("    end")
    P("")
    P("    // ---- 64-bucket log histogram of per-run latency (lat_ctr at completion) -")
    P("    // bucket = min(leading_one,15)*4 + 2 mantissa bits below the leading one.")
    P("    // ~19% resolution per bucket, 16 octaves -- see harness spec.  Computed")
    P("    // once per run completion (not every cycle), so it costs nothing on the")
    P("    // async kernel's own critical path and is cheap even at 250 MHz.")
    P("    reg [31:0] hist [0:63];")
    P("    integer hi;")
    P("    reg [4:0]  lead1;")
    P("    reg        found1;")
    P("    reg [1:0]  mant;")
    P("    reg [5:0]  bucket;")
    P("    always @(*) begin")
    P("        found1 = 1'b0;")
    P("        lead1  = 5'd0;")
    P("        for (hi = 31; hi >= 0; hi = hi - 1)")
    P("            if (!found1 && lat_ctr[hi]) begin lead1 = hi[4:0]; found1 = 1'b1; end")
    P("        if (lead1 >= 5'd2)")
    P("            mant = lat_ctr[lead1-1 -: 2];")
    P("        else if (lead1 == 5'd1)")
    P("            mant = {lat_ctr[0], 1'b0};")
    P("        else")
    P("            mant = 2'b00;")
    P("        bucket = (lead1 > 5'd15 ? 6'd15 : lead1[3:0]) * 6'd4 + {4'b0, mant};")
    P("    end")
    P("")
    P("    always @(posedge aclk or negedge aresetn) begin")
    P("        if (!aresetn) begin")
    P("            st <= S_IDLE; bench_busy <= 1'b0; bench_done <= 1'b0;")
    P("            bench_set_req <= 1'b0; bench_o_ack <= 1'b0;")
    P("            runs_done <= 32'b0; lat_ctr <= 32'b0; prep_ctr <= 32'b0;")
    P("            cycles <= 32'b0; prep_cycles <= 32'b0;")
    P("            lat_min <= 32'hFFFFFFFF; lat_max <= 32'b0;")
    P("            lfsr <= 32'h1; bench_op0 <= 32'b0; bench_op1 <= 32'b0;")
    P("            last_op0 <= 32'b0; last_op1 <= 32'b0; start_d <= 1'b0;")
    P("            sig <= 32'b0; mismatch_sticky <= 1'b0; mismatch_idx <= 32'b0;")
    P("            mismatch_val <= 32'b0; mismatch_ref <= 32'b0; have_ref <= 1'b0;")
    P("            for (hi = 0; hi < 64; hi = hi + 1) hist[hi] <= 32'b0;")
    P("        end else begin")
    P("            start_d <= bctrl_start;")
    P("            bench_set_req <= 1'b0;")
    P("")
    P("            if (bctrl_rst) begin")
    P("                st <= S_IDLE; bench_busy <= 1'b0; bench_done <= 1'b0;")
    P("                bench_o_ack <= 1'b0; runs_done <= 32'b0; cycles <= 32'b0;")
    P("                prep_cycles <= 32'b0;")
    P("                lat_min <= 32'hFFFFFFFF; lat_max <= 32'b0;")
    P("                sig <= 32'b0; mismatch_sticky <= 1'b0; mismatch_idx <= 32'b0;")
    P("                mismatch_val <= 32'b0; mismatch_ref <= 32'b0; have_ref <= 1'b0;")
    P("                for (hi = 0; hi < 64; hi = hi + 1) hist[hi] <= 32'b0;")
    P("            end else begin")
    P("                // CYCLES excludes S_PREP settling (measurement defect item in the")
    P("                // spec); PREP_CYCLES accumulates the same window separately so it")
    P("                // is reported, never silently dropped.")
    P("                if (bench_busy && st == S_PREP && prep_cycles != 32'hFFFFFFFF)")
    P("                    prep_cycles <= prep_cycles + 1;")
    P("                if (bench_busy && st != S_PREP && cycles != 32'hFFFFFFFF)")
    P("                    cycles <= cycles + 1;")
    P("                if (st != S_IDLE && st != S_NEXT) lat_ctr <= lat_ctr + 1;")
    P("")
    P("                case (st)")
    P("                    S_IDLE: if (start_rise && n_runs != 32'b0) begin")
    P("                        bench_busy <= 1'b1; bench_done <= 1'b0;")
    P("                        runs_done  <= 32'b0; cycles <= 32'b0; prep_cycles <= 32'b0;")
    P("                        lat_min    <= 32'hFFFFFFFF; lat_max <= 32'b0;")
    P("                        sig <= 32'b0; mismatch_sticky <= 1'b0; have_ref <= 1'b0;")
    P("                        lfsr       <= (op0 == 32'b0) ? 32'h1 : op0;")
    P("                        st         <= S_PREP;")
    P("                        // hist[] must reset every batch, same as runs_done/lat_min/")
    P("                        // lat_max/sig above -- otherwise back-to-back batches (no")
    P("                        // explicit BCTRL.bench_rst between them) silently accumulate")
    P("                        // into one histogram and the host reads a corrupted per-batch")
    P("                        // distribution.  Found via the sum(hist)==run_count check.")
    P("                        for (hi = 0; hi < 64; hi = hi + 1) hist[hi] <= 32'b0;")
    P("                    end")
    P("")
    P("                    // Draw this run's operands.  UNIFORM (mode 0, default): each")
    P("                    // word is a fresh full-width LFSR state -- genuinely uniform,")
    P("                    // unlike gcd_bench.v's old masked-odd LFSR.  FIXED (mode 1):")
    P("                    // rerun op0/op1 verbatim, which is what makes the repeatability")
    P("                    // latch below meaningful.  LEGACY (mode 2): the original biased")
    P("                    // encoding, kept for A/B comparison only.")
    P("                    S_PREP: begin")
    P("                        if (prep_ctr == 32'd0) begin")
    P("                            case (bctrl_mode)")
    fixed0, fixed1 = apply_domain_masks(kernel, data_args, "op0", "op1")
    P(f"                                2'd1: begin bench_op0 <= {fixed0}; bench_op1 <= {fixed1}; end")
    legacy0, legacy1 = apply_domain_masks(
        kernel, data_args,
        "({8'b0, lfsr[23:0]} | 32'd1)",
        "({8'b0, {lfsr[11:0], lfsr[23:12]}} | 32'd1)")
    P("                                2'd2: begin")
    P(f"                                    bench_op0 <= {legacy0};")
    P(f"                                    bench_op1 <= {legacy1};")
    P("                                    lfsr <= {lfsr[30:0], lfsr[31]^lfsr[21]^lfsr[1]^lfsr[0]};")
    P("                                end")
    uni0, uni1 = apply_domain_masks(kernel, data_args, "lfsr", "lfsr_n1")
    P("                                default: begin")
    P("                                    // lfsr_n1/lfsr_n2 (declared above) are two successive")
    P("                                    // LFSR states computed combinationally from the CURRENT")
    P("                                    // lfsr, so op0/op1/next-seed all update from one")
    P("                                    // consistent snapshot instead of racing on lfsr being")
    P("                                    // written twice in one always block.  Any domain mask")
    P("                                    // (see gen_bench.py header) is applied HERE, inline in")
    P("                                    // the same non-blocking assignment that draws the word --")
    P("                                    // NOT as a separate later assignment to the same reg,")
    P("                                    // which would silently re-mask last run's stale value")
    P("                                    // instead of this run's fresh draw (NBA read-before-")
    P("                                    // write: a later `bench_opN <= bench_opN & mask` in this")
    P("                                    // block would read the PRE-edge bench_opN, discarding")
    P("                                    // the draw above it entirely).")
    P(f"                                    bench_op0 <= {uni0};")
    P(f"                                    bench_op1 <= {uni1};")
    P("                                    lfsr <= lfsr_n2;")
    P("                                end")
    P("                            endcase")
    P("                        end")
    P("                        prep_ctr <= prep_ctr + 1;")
    P("                        // >= not ==: run_gap is host-writable and could be")
    P("                        // changed mid-batch, and == would sail past a lowered")
    P("                        // target and wrap 2^32 cycles later, which would look")
    P("                        // exactly like the hang this knob exists to diagnose.")
    P("                        if (prep_ctr >= run_gap) begin")
    P("                            prep_ctr <= 32'b0; lat_ctr <= 32'b0; st <= S_ISSUE;")
    P("                        end")
    P("                    end")
    P("")
    P("                    S_ISSUE: begin bench_set_req <= 1'b1; st <= S_WAIT_ACK; end")
    P("                    S_WAIT_ACK: if (i_ack_latched) st <= S_WAIT_RES;")
    P("")
    P("                    S_WAIT_RES: if (o_req_latched) begin")
    P("                        last_op0 <= bench_op0; last_op1 <= bench_op1;")
    P("                        if (lat_ctr < lat_min) lat_min <= lat_ctr;")
    P("                        if (lat_ctr > lat_max) lat_max <= lat_ctr;")
    P("                        hist[bucket] <= (hist[bucket] == 32'hFFFFFFFF) ? hist[bucket] : hist[bucket] + 1;")
    P("                        // SIG is deliberately NOT updated here anymore -- see S_NEXT")
    P("                        // below. This state's own comment used to claim o_data_pl is")
    P("                        // \"already stable\" at this edge because it is combinational")
    P("                        // off operands held steady for the whole transaction. That")
    P("                        // claim was WRONG on real silicon: board.sh cross-checks")
    P("                        // (hw/run_gcd_sig_check.sh, gcd) bisected a SIG mismatch down")
    P("                        // to exactly this read -- the offending run's own last_op0/")
    P("                        // last_op1 and its o_data_capture-based ODATA readback (taken")
    P("                        // much later) both matched the host's independent replica")
    P("                        // exactly, and driving the SAME operand pair through FIXED")
    P("                        // mode 50/50 times also reproduced the correct answer -- so")
    P("                        // the compiled kernel was right and this direct read of the")
    P("                        // raw combinational o_data_pl, at the exact clock edge")
    P("                        // o_req_latched first goes high, was catching it mid-settle.")
    P("                        // Repeatable across sim (green throughout) because sim does")
    P("                        // not model the real routed settling delay on this net --")
    P("                        // only the board caught it, and non-deterministically (two")
    P("                        // otherwise-identical board runs produced two different wrong")
    P("                        // SIG values), consistent with a timing race rather than a")
    P("                        // logic bug.")
    P("                        // Repeatability latch: meaningful in FIXED mode, where every")
    P("                        // run's operands are identical, so a correct deterministic")
    P("                        // circuit must return the identical result every time.  Any")
    P("                        // divergence is latched (sticky) with the failing run's index")
    P("                        // and observed value, against the run-0 reference.")
    P("                        // NOTE: this still reads o_data_pl directly, same class of")
    P("                        // risk as SIG had -- not fixed here (out of scope for the SIG")
    P("                        // race fix), flagged for whoever looks at this next. It was")
    P("                        // not observed to misfire in any run so far, but FIXED mode")
    P("                        // reruns the SAME operands every time, which is exactly the")
    P("                        // condition that was seen to mask the SIG race too (the")
    P("                        // isolated 50-run FIXED-mode probe on the pair that broke SIG")
    P("                        // never triggered this latch either).")
    P("                        if (bctrl_mode == 2'd1) begin")
    P("                            if (!have_ref) begin")
    P("                                have_ref <= 1'b1; mismatch_ref <= o_data_pl;")
    P("                            end else if (!mismatch_sticky && o_data_pl != mismatch_ref) begin")
    P("                                mismatch_sticky <= 1'b1;")
    P("                                mismatch_idx <= runs_done;")
    P("                                mismatch_val <= o_data_pl;")
    P("                            end")
    P("                        end")
    P("                        bench_o_ack <= 1'b1;")
    P("                        st <= S_ACK;")
    P("                    end")
    P("")
    P("                    S_ACK: st <= S_RTZ;")
    P("                    S_RTZ: if (!o_req_s) begin bench_o_ack <= 1'b0; st <= S_NEXT; end")
    P("                    S_NEXT: begin")
    P("                        // signature: rotate-left-1 then XOR in this run's result --")
    P("                        // cheap (one 32-bit XOR+rotate), and the host replays the")
    P("                        // identical LFSR sequence in software to compute the same")
    P("                        // value from the seed alone. Reads o_data_capture (the")
    P("                        // ALREADY-REGISTERED, free-running one-cycle mirror of")
    P("                        // o_data_pl -- see its declaration/assignment above), not the")
    P("                        // raw combinational o_data_pl, and reads it here in S_NEXT")
    P("                        // rather than back in S_WAIT_RES. No new state or wait cycle")
    P("                        // was added to get this margin: S_NEXT already runs exactly")
    P("                        // once per run (same guarantee SIG always had), several clock")
    P("                        // edges after o_req_latched first rose (S_ACK, then however")
    P("                        // long S_RTZ takes to observe o_req_s fall through its own")
    P("                        // 2-flop synchronizer) -- and bench_op0/bench_op1 do not")
    P("                        // change until the NEXT run's S_PREP, well after S_NEXT, so")
    P("                        // o_data_pl (and therefore o_data_capture, one cycle behind")
    P("                        // it) has had that whole window to finish settling before")
    P("                        // this read, instead of being sampled at the single edge the")
    P("                        // completion pulse first arrives on.")
    P("                        sig <= {sig[30:0], sig[31]} ^ o_data_capture;")
    P("                        runs_done <= runs_done + 1;")
    P("                        if (runs_done + 1 >= n_runs) begin")
    P("                            bench_busy <= 1'b0; bench_done <= 1'b1; st <= S_IDLE;")
    P("                        end else st <= S_PREP;")
    P("                    end")
    P("                    default: st <= S_IDLE;")
    P("                endcase")
    P("            end")
    P("        end")
    P("    end")
    P("")
    P("    // ---- AXI slave ----------------------------------------------------------")
    P("    always @(posedge aclk or negedge aresetn) begin")
    P("        if (!aresetn) begin")
    P("            axi_awready <= 1'b0; axi_wready <= 1'b0; axi_bvalid <= 1'b0;")
    P("            axi_arready <= 1'b0; axi_rvalid <= 1'b0;")
    P("            axi_bid <= 12'b0;    axi_rid <= 12'b0;   aw_en <= 1'b1;")
    P("            ctrl_i_req <= 1'b0;  ctrl_o_ack <= 1'b0; ctrl_rst <= 1'b1;")
    P("            op0 <= 32'b0; op1 <= 32'b0;")
    P("            n_runs <= 32'b0;")
    P("            run_gap <= 32'd15;   // matches the original fixed prep_ctr==15")
    P("            bctrl_start <= 1'b0; bctrl_rst <= 1'b0; bctrl_mode <= 2'b0;")
    P("            sync_i_ack <= 2'b0;  sync_o_req <= 2'b0; o_data_capture <= 32'b0;")
    P("        end else begin")
    P("            sync_i_ack <= {sync_i_ack[0], i_ack_host};")
    P("            sync_o_req <= {sync_o_req[0], o_req_pl};")
    P("            o_data_capture <= o_data_pl;")
    P("")
    P("            if (~axi_awready && awvalid && wvalid && aw_en) begin")
    P("                axi_awready <= 1'b1; axi_wready <= 1'b1;")
    P("                axi_awaddr  <= awaddr[8:2];")
    P("                axi_bid     <= awid;")
    P("                aw_en       <= 1'b0;")
    P("            end else begin")
    P("                axi_awready <= 1'b0; axi_wready <= 1'b0;")
    P("                if (bvalid && bready) aw_en <= 1'b1;")
    P("            end")
    P("")
    P("            if (do_write) begin")
    P("                case (axi_awaddr)")
    P("                    7'h0: begin ctrl_i_req <= wdata[0]; ctrl_o_ack <= wdata[1]; ctrl_rst <= wdata[2]; end")
    P("                    7'h2: op0       <= wdata;")
    P("                    7'h3: op1       <= wdata;")
    P("                    7'h5: n_runs    <= wdata;")
    P("                    7'h14: run_gap  <= wdata;   // inter-run gap, aclk cycles")
    P("                    7'h8: begin bctrl_start <= wdata[0]; bctrl_rst <= wdata[1]; bctrl_mode <= wdata[3:2]; end")
    P("                    default: ;")
    P("                endcase")
    P("            end")
    P("")
    P("            if (do_write && ~axi_bvalid) axi_bvalid <= 1'b1;")
    P("            else if (bready && axi_bvalid) axi_bvalid <= 1'b0;")
    P("")
    P("            if (~axi_arready && arvalid) begin")
    P("                axi_arready <= 1'b1; axi_araddr <= araddr[8:2]; axi_rid <= arid;")
    P("            end else axi_arready <= 1'b0;")
    P("")
    P("            if (axi_arready && arvalid && ~axi_rvalid) axi_rvalid <= 1'b1;")
    P("            else if (axi_rvalid && rready) axi_rvalid <= 1'b0;")
    P("        end")
    P("    end")
    P("")
    P("    reg [31:0] rdata_r;")
    P("    always @(*) begin")
    P("        casez (axi_araddr)")
    P("            7'h00: rdata_r = {29'b0, ctrl_rst, ctrl_o_ack, ctrl_i_req};")
    P("            7'h01: rdata_r = {30'b0, o_req_s, i_ack_s};")
    P("            7'h02: rdata_r = op0;")
    P("            7'h03: rdata_r = op1;")
    P("            7'h04: rdata_r = o_data_capture;")
    P("            7'h05: rdata_r = n_runs;")
    P("            7'h14: rdata_r = run_gap;")
    P("            7'h06: rdata_r = cycles;")
    P("            7'h07: rdata_r = prep_cycles;")
    P("            7'h08: rdata_r = {28'b0, bctrl_mode, bctrl_rst, bctrl_start};")
    P("            7'h09: rdata_r = {runs_done[15:0], 14'b0, bench_done, bench_busy};")
    P("            7'h0A: rdata_r = lat_min;")
    P("            7'h0B: rdata_r = lat_max;")
    P("            7'h0C: rdata_r = last_op0;")
    P("            7'h0D: rdata_r = last_op1;")
    P("            7'h0E: rdata_r = sig;")
    P("            7'h0F: rdata_r = {31'b0, mismatch_sticky};")
    P("            7'h10: rdata_r = mismatch_idx;")
    P("            7'h11: rdata_r = mismatch_val;")
    P("            7'h12: rdata_r = mismatch_ref;")
    P(f"            7'h13: rdata_r = {{16'd{nargs}, 8'd{data_args[0].width if data_args else 0}, "
      f"8'd{data_args[-1].width if data_args else 0}}}; // {{nargs, arg0_width, argN_width}} metadata")
    P("            7'b1zzzzzz: rdata_r = hist[axi_araddr[5:0]];  // 0x40-0x7F word range -> hist[0..63]")
    P("            default: rdata_r = 32'b0;")
    P("        endcase")
    P("    end")
    P("    assign rdata = rdata_r;")
    P("")
    P("    // ---- the kernel and its environment --------------------------------------")
    n_fork = nargs + 1
    fork_ack_list = ", ".join(["start_ack"] + [a.name + "_ack" for a in reversed(data_args)])
    P(f"    wire [{n_fork - 1}:0] in_req;")
    P(f"    wire start_ack;")
    for a in data_args:
        P(f"    wire {a.name}_ack;")
    P("    wire p_end_req, p_end_ack;")
    P("")
    P(f"    bd_fork #(.N({n_fork})) ufork (")
    P(f"        .rst(rst_pl), .req(i_req_pl), .ack(i_ack_pl),")
    P(f"        .req_out(in_req), .ack_in({{{fork_ack_list}}}));")
    P("")
    P("    bd_delay #(.N(2)) upsnk (.a(p_end_req), .z(p_end_ack));")
    P("")
    P(f"    {dut_module} udut (")
    P(f"        .rst       (rst_pl),")
    # Word wiring: for our 6 kernels nargs<=2 and each arg maps to a
    # contiguous, word-aligned slice of {op1_to_core,op0_to_core}.
    word_idx = 0
    core_exprs = []
    for a in data_args:
        nw = words_for(a.width)
        lo, hi = word_idx, word_idx + nw - 1
        if nw == 1:
            expr = f"op{lo}_to_core"
        else:
            expr = "{" + ", ".join(f"op{w}_to_core" for w in range(hi, lo - 1, -1)) + "}"
        core_exprs.append((a, expr))
        word_idx += nw
    for i, (a, expr) in enumerate(core_exprs):
        P(f"        .{a.name}_req  (in_req[{i}]), .{a.name}_ack  ({a.name}_ack), .{a.name}_data ({expr}),")
    P(f"        .start_req (in_req[{nargs}]), .start_ack (start_ack),")
    P(f"        .out0_req  (o_req_pl),  .out0_ack  (o_ack_pl),  .out0_data (o_data_pl),")
    P(f"        .p_end_req (p_end_req), .p_end_ack (p_end_ack));")
    P("")
    P("    assign core_i_ack = i_ack_pl;")
    P("    assign core_o_req = o_req_pl;")
    P("")
    P(f"endmodule")
    P("")

    # -------------------------------------------------------------------
    # top module (PS7 shell)
    P(f"module {top_name} (")
    P("    output led_red,")
    P("    output led_green")
    P(");")
    P("")
    P("    wire [3:0]  fclkclk;")
    P("    wire        fclk0_bufg;")
    P("    wire        aresetn;")
    P("    wire        m_axi_gp0_aclk = fclk0_bufg;")
    P("")
    P("    wire        awvalid, awready;")
    P("    wire [31:0] awaddr;")
    P("    wire [11:0] awid;")
    P("    wire        wvalid, wready;")
    P("    wire [31:0] wdata;")
    P("    wire [3:0]  wstrb;")
    P("    wire        bvalid, bready;")
    P("    wire [1:0]  bresp;")
    P("    wire [11:0] bid;")
    P("    wire        arvalid, arready;")
    P("    wire [31:0] araddr;")
    P("    wire [11:0] arid;")
    P("    wire        rvalid, rready;")
    P("    wire [31:0] rdata;")
    P("    wire [1:0]  rresp;")
    P("    wire [11:0] rid;")
    P("")
    P("    PS7 ps7_i (")
    P("        .MAXIGP0ACLK    (m_axi_gp0_aclk),")
    P("        .MAXIGP0ARESETN (aresetn),")
    P("        .MAXIGP0AWVALID (awvalid), .MAXIGP0AWREADY (awready),")
    P("        .MAXIGP0AWADDR  (awaddr),  .MAXIGP0AWID    (awid),")
    P("        .MAXIGP0WVALID  (wvalid),  .MAXIGP0WREADY  (wready),")
    P("        .MAXIGP0WDATA   (wdata),   .MAXIGP0WSTRB   (wstrb),")
    P("        .MAXIGP0BVALID  (bvalid),  .MAXIGP0BREADY  (bready),")
    P("        .MAXIGP0BRESP   (bresp),   .MAXIGP0BID     (bid),")
    P("        .MAXIGP0ARVALID (arvalid), .MAXIGP0ARREADY (arready),")
    P("        .MAXIGP0ARADDR  (araddr),  .MAXIGP0ARID    (arid),")
    P("        .MAXIGP0RVALID  (rvalid),  .MAXIGP0RREADY  (rready),")
    P("        .MAXIGP0RDATA   (rdata),   .MAXIGP0RRESP   (rresp),")
    P("        .MAXIGP0RLAST   (1'b1),    .MAXIGP0RID     (rid),")
    P("        .FCLKCLK        (fclkclk),")
    P("        .FCLKRESETN     (),")
    P("        .FCLKCLKTRIGN   (4'b0)")
    P("    );")
    P("")
    P("    BUFG bufg_fclk0 (.I(fclkclk[0]), .O(fclk0_bufg));")
    P("")
    P("    wire core_i_ack, core_o_req;")
    P("")
    P(f"    {bridge} bridge_i (")
    P("        .aclk    (m_axi_gp0_aclk), .aresetn (aresetn),")
    P("        .awvalid (awvalid), .awready (awready), .awaddr (awaddr), .awid (awid),")
    P("        .wvalid  (wvalid),  .wready  (wready),  .wdata  (wdata),  .wstrb (wstrb),")
    P("        .bvalid  (bvalid),  .bready  (bready),  .bresp  (bresp),  .bid   (bid),")
    P("        .arvalid (arvalid), .arready (arready), .araddr (araddr), .arid  (arid),")
    P("        .rvalid  (rvalid),  .rready  (rready),  .rdata  (rdata),")
    P("        .rresp   (rresp),   .rid     (rid),")
    P("        .core_i_ack (core_i_ack), .core_o_req (core_o_req)")
    P("    );")
    P("")
    P("    assign led_red   = core_i_ack;")
    P("    assign led_green = core_o_req;")
    P("")
    P("endmodule")
    P("`default_nettype wire")
    return "\n".join(lines)


def apply_domain_masks(kernel, data_args, raw0, raw1):
    """Given the UNMASKED Verilog expressions that would be drawn into
    bench_op0/bench_op1 this cycle (raw0, raw1 -- e.g. 'lfsr'/'lfsr_n1' for
    UNIFORM, 'op0'/'op1' for FIXED), return the MASKED expressions that
    should actually be assigned, per the kernel's DOMAIN_RESTRICTIONS.

    Masking is applied to the raw expression INLINE, in the same
    non-blocking assignment that draws the word -- never as a later,
    separate assignment to the same reg (see the S_PREP comment in emit()
    for why that reads stale data under Verilog's NBA semantics).
    """
    restr = DOMAIN_RESTRICTIONS.get(kernel, {})
    raw = {0: raw0, 1: raw1}
    masked = dict(raw)
    word_idx = 0
    for a in data_args:
        nw = words_for(a.width)
        lo, hi = word_idx, word_idx + nw - 1
        rule = restr.get(a.name)
        if rule is not None:
            if rule["kind"] == "positive_nonzero":
                masked[hi] = f"(({raw[hi]}) & 32'h7FFFFFFF)"
                if lo == hi:
                    masked[lo] = f"((({raw[lo]}) & 32'h7FFFFFFF) == 32'h0 ? 32'h1 : (({raw[lo]}) & 32'h7FFFFFFF))"
                else:
                    zero_check = " && ".join(f"(({raw[w]}) == 32'h0)" for w in range(lo, hi))
                    masked[lo] = (f"(({zero_check} && (({raw[hi]}) & 32'h7FFFFFFF) == 32'h0) "
                                  f"? 32'h1 : ({raw[lo]}))")
            elif rule["kind"] == "and_mask":
                masked[lo] = f"(({raw[lo]}) & {rule['value']})"
            elif rule["kind"] == "nonnegative":
                # Clear the sign bit only -- zero is a legitimate, already-
                # handled input (gcd.c's a==0/b==0 early return), unlike
                # collatz's positive_nonzero which must also exclude zero.
                for w in range(lo, hi + 1):
                    masked[w] = f"(({raw[w]}) & 32'h7FFFFFFF)" if w == hi else raw[w]
        word_idx += nw
    return masked[0], masked[1]


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                  formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("kernel", help="kernel name, e.g. gcd, ipow, collatz, collatz64, isprime, xorshift")
    ap.add_argument("-o", "--out", required=True, help="output Verilog path")
    ap.add_argument("--top", help="top module name (default: <kernel>_bench or <kernel>_null_bench)")
    ap.add_argument("--null", action="store_true",
                     help="generate the null-kernel control (same signature, trivial pass-through DUT)")
    args = ap.parse_args()

    top_name = args.top or (f"{args.kernel}_null_bench" if args.null else f"{args.kernel}_bench")
    text = emit(args.kernel, args.null, top_name)
    os.makedirs(os.path.dirname(args.out) or ".", exist_ok=True)
    with open(args.out, "w") as f:
        f.write(text)
    print(f"wrote {args.out}: module {top_name} ({'null' if args.null else 'real'} DUT for {args.kernel})")


if __name__ == "__main__":
    main()
