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
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "bdc"))
from hs import parse  # noqa: E402

# THE OPERAND FILE (suiteb, 2026-11-17).  It was two words, OP0/OP1 at 7'h02/7'h03, because each of the six original
# kernels needed at most two.  The benchmark suite has kernels with more arguments, so the file is now up to
# MAX_WORDS words: OP0/OP1 where they always were, OP2..OP9 at 7'h18..7'h1F (byte 0x60..0x7C).  The extra registers
# are emitted ONLY for a kernel that needs more than two words, so for every kernel that needs two or fewer --
# all six of the originals among them -- this generator's output is byte-identical to what it was.  Arguments map
# onto words in signature order, an i64 as its low word then its high word (research/data/suite/bench/README.md).
MAX_WORDS = 10
OPX_BASE = 0x18          # word address of OP2; OPk is at OPX_BASE + k - 2

# A memref argument is not an operand word: it is a memory behind bdc/emit.py --host-mem's host port, which the bench
# drives through the MEM* registers below (research/data/suite/bench/README.md).  Word addresses:
MEM_ADDR, MEM_WDATA, MEM_CMD, MEM_STAT, MEM_RDATA = 0x20, 0x21, 0x22, 0x23, 0x24
LAYOUT, MEMINFO_BASE = 0x28, 0x30   # LAYOUT {nmem, nwords, 16'hB5C2}; MEMINFO[m] {depth, elem width, addr width}
LAYOUT_MAGIC = 0xB5C2
MAX_MEMS = 8
HOST_TIMEOUT = 0x7FF     # aclk cycles a host access may wait for the port before it is abandoned (and flagged)

# Per-kernel operand domain restriction: kernel name -> list of one entry per
# data arg, each either None (no restriction) or a dict describing the mask.
# 'positive_nonzero' clears the top bit of the arg's OWN width and remaps an
# all-zero result to 1.  'and_mask' ANDs the low 32 bits of that arg's first
# word with the given constant (used for xorshift's rounds).
DOMAIN_RESTRICTIONS = {
    # The mask is per-kernel because the binding constraint is not the START
    # value, it is the trajectory PEAK -- Collatz climbs far above its seed
    # before descending, and it is the peak that has to stay inside the C
    # type.  Both numbers below are computed, not guessed (see the note in
    # apply_domain_masks):
    #   collatz   (int32): every n <= 0xFFFF peaks at most 593,279,152
    #                      (at n=60975), inside INT32_MAX.  The next mask up,
    #                      0x3FFFF, peaks at 1.7e10 and does not fit.
    #   collatz64 (int64): masking the HIGH word to zero leaves n <= 2**32-1,
    #                      whose sampled peak is 3.06e14 -- 30000x inside
    #                      INT64_MAX.
    "collatz":   {"n": {"kind": "positive_nonzero", "mask": "32'h0000FFFF"}},
    "collatz64": {"n": {"kind": "positive_nonzero", "mask": "32'h00000000"}},
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



RE_KERNEL_PARAM = re.compile(r"parameter\s+DELAY_(\w+)\s*=\s*(\d+)")


def kernel_delay_params(dut_module):
    """[(instance, default links)] read off the emitted kernel's own header.

    The names are PARSED OUT OF THE KERNEL, never written down here.  A second
    hardcoded list of instance names is exactly the failure bdc/emit.py's header
    warns about twice: get the key wrong and the tightening loop reports success
    having changed nothing any source file reads, and every other gate still
    passes.

    Returns [] when the kernel declares no delay parameters.  When the kernel
    FILE is missing it says so on stderr rather than returning [] quietly --
    silently emitting a bench with no overrides is the same failure one level up.
    """
    here = os.path.dirname(os.path.abspath(__file__))
    stem = dut_module[4:] if dut_module.startswith("bdc_") else dut_module
    for c in (os.path.join(here, "..", "build", "gen", stem + "_kernel_bench.v"),
              os.path.join("build", "gen", stem + "_kernel_bench.v")):
        if os.path.exists(c):
            m = re.search(r"module\s+" + re.escape(dut_module) + r"\s*#\((.*?)\)\s*\(",
                          open(c).read(400000), re.S)
            return [(i, int(d)) for i, d in RE_KERNEL_PARAM.findall(m.group(1))] if m else []
    print("gen_bench.py: WARNING -- no kernel file for %s under build/gen/, so the "
          "bench gets no per-instance delay overrides and verify/tighten.py's "
          "proposals will have nothing to attach to" % dut_module, file=sys.stderr)
    return []

# bdc/emit.py's portname(): an argName/resName as a Verilog port base.  Repeated here rather than imported because
# importing emit.py reads its build-time environment knobs (BDC_SELECT_PADS and friends) at import time.
_RESERVED = {
    "end", "begin", "module", "wire", "reg", "input", "output", "inout",
    "assign", "always", "initial", "parameter", "localparam", "generate",
    "endmodule", "case", "default", "function", "task", "and", "or", "not",
    "buf", "xor", "nand", "nor", "xnor", "if", "else", "for", "while",
}


def portname(name):
    s = re.sub(r"[^A-Za-z0-9_]", "_", name)
    return "p_" + s if s in _RESERVED or not s[:1].isalpha() else s


def host_mem_lines(mems):
    """The bench's side of bdc/emit.py --host-mem's host ports: registers, a
    four-phase sequencer in the aclk domain, one 2-flop synchroniser per
    acknowledge.  Emitted only for a kernel with memref arguments."""
    nm = len(mems)
    L = []
    A = L.append
    A("    // ---- the host memory path (gen_bench.py host_mem_lines) ---------------------------------------")
    A("    // Each memref argument's memory has a HOST PORT: bdc/emit.py --host-mem gave its bdc_memport one more")
    A("    // one-hot slot, wired to the kernel's <m>_host_* ports.  This sequencer drives those slots from the")
    A("    // PS side, one access at a time, so the host can fill an array before a call and read it back after:")
    A("    //   MEMADDR  7'h20 RW [15:0] element index, [23:16] memory (signature order of the memref args)")
    A("    //   MEMWDATA 7'h21 W  mem[MEMADDR] <= wdata, then index += 1.  R: MEMRDATA")
    A("    //   MEMCMD   7'h22 W  [0]=1: MEMRDATA <= mem[MEMADDR], then index += 1")
    A("    //   MEMSTAT  7'h23 R  [0] busy [1] refused (sticky) [2] timeout (sticky) [31:16] accesses done;")
    A("    //                   W  clears [1], [2] and the count")
    A("    //   MEMRDATA 7'h24 R  the word the last access read (a write reads back what it wrote: WRITE_FIRST)")
    A("    // The AXI response to a MEMWDATA/MEMCMD write is held until the access is over, so a run of writes")
    A("    // paces itself and a read's data is in MEMRDATA by the time its write response arrives.")
    A("    //")
    A("    // The slot is ONE-HOT with the kernel's own (the plain bdc_memport's obligation on its caller): an")
    A("    // access is REFUSED (MEMSTAT[1], the write still answered) while a batch runs or the kernel is held")
    A("    // in reset (its port's acknowledge C-tree is reset with it, so the access could never finish).  So")
    A("    // the host uses the port between calls only.  Before raising its request the sequencer also waits")
    A("    // for the port's SHARED acknowledge to be low: the last access, the kernel's or its own, has")
    A("    // returned to zero, so this request makes a fresh rising edge on the RAM's manufactured clock.")
    A("    //")
    A("    // Every acknowledge is an asynchronous signal entering this clocked FSM, so each gets a 2-flop")
    A("    // synchroniser (CLAUDE.md) and is never read raw.  Address, data and we are flops set one aclk")
    A("    // BEFORE the request rises and held until the acknowledge has been seen low again: the bundling")
    A("    // margin is a whole clock period on top of the port's own DSETUP.  The read data is sampled once")
    A("    // the synchronised acknowledge is high, two clocks after the RAM produced it and while it holds.")
    A("    localparam M_IDLE = 2'd0, M_REQ = 2'd1, M_ACK = 2'd2, M_RTZ = 2'd3;")
    A("    reg [1:0]  mst;")
    A("    reg [15:0] mem_idx, mem_count;")
    A("    reg [7:0]  mem_sel;")
    A("    reg [31:0] mem_wd, mem_rd;")
    A("    reg        mem_we, mem_busy, mem_resp, mem_refused, mem_timeout;")
    A("    reg [10:0] mem_tmo;")
    A(f"    reg [{nm - 1}:0] mem_hreq;")
    for m, (name, depth, dw, aw) in enumerate(mems):
        A(f"    wire       mem_hack{m};                  // {name}: the port's acknowledge (async)")
        A(f"    wire [{dw - 1}:0] mem_hrd{m};")
        A(f"    reg  [1:0] sync_hack{m};")
    sel_ack = " : ".join(f"(mem_sel == 8'd{m}) ? sync_hack{m}[1]" for m in range(nm)) + " : 1'b0"
    A(f"    wire       hack_s = {sel_ack};")
    sel_rd = " : ".join(f"(mem_sel == 8'd{m}) ? {{{32 - dw}'b0, mem_hrd{m}}}" if dw < 32
                        else f"(mem_sel == 8'd{m}) ? mem_hrd{m}"
                        for m, (_, _, dw, _) in enumerate(mems)) + " : 32'b0"
    A(f"    wire [31:0] hrd_sel = {sel_rd};")
    A("    wire       mem_cmd   = do_write && (axi_awaddr == 7'h21 || (axi_awaddr == 7'h22 && wdata[0]));")
    A(f"    wire       mem_ok    = !mem_busy && !bench_busy && !ctrl_rst && (mem_sel < 8'd{nm});")
    A("    wire       mem_start = mem_cmd && mem_ok;")
    onehot = "{" + ", ".join(f"mem_sel == 8'd{m}" for m in reversed(range(nm))) + "}"
    A("    always @(posedge aclk or negedge aresetn) begin")
    A("        if (!aresetn) begin")
    A("            mst <= M_IDLE; mem_idx <= 16'b0; mem_count <= 16'b0; mem_sel <= 8'b0;")
    A("            mem_wd <= 32'b0; mem_rd <= 32'b0; mem_we <= 1'b0; mem_busy <= 1'b0; mem_resp <= 1'b0;")
    A(f"            mem_refused <= 1'b0; mem_timeout <= 1'b0; mem_tmo <= 11'b0; mem_hreq <= {nm}'b0;")
    A("            " + " ".join(f"sync_hack{m} <= 2'b0;" for m in range(nm)))
    A("        end else begin")
    A("            " + " ".join(f"sync_hack{m} <= {{sync_hack{m}[0], mem_hack{m}}};" for m in range(nm)))
    A("            mem_resp <= 1'b0;")
    A("            if (do_write && axi_awaddr == 7'h20) begin mem_idx <= wdata[15:0]; mem_sel <= wdata[23:16]; end")
    A("            if (do_write && axi_awaddr == 7'h23) begin mem_refused <= 1'b0; mem_timeout <= 1'b0; mem_count <= 16'b0; end")
    A("            if (mem_cmd && !mem_ok) mem_refused <= 1'b1;")
    A("            case (mst)")
    A("                M_IDLE: if (mem_start) begin")
    A("                    mem_we <= (axi_awaddr == 7'h21);")
    A("                    if (axi_awaddr == 7'h21) mem_wd <= wdata;")
    A("                    mem_busy <= 1'b1; mem_tmo <= 11'b0; mst <= M_REQ;")
    A("                end")
    A("                // address, data and we have been stable since the last edge; ask once the port is quiet")
    A(f"                M_REQ: if (!hack_s) begin mem_hreq <= {onehot}; mst <= M_ACK; end")
    A("                M_ACK: if (hack_s) begin mem_rd <= hrd_sel; mem_hreq <= " + f"{nm}'b0; mst <= M_RTZ; end")
    A("                M_RTZ: if (!hack_s) begin")
    A("                    mst <= M_IDLE; mem_busy <= 1'b0; mem_resp <= 1'b1;")
    A("                    mem_idx <= mem_idx + 16'd1; mem_count <= mem_count + 16'd1;")
    A("                end")
    A("            endcase")
    A("            // No acknowledge for HOST_TIMEOUT cycles: abandon the access, flag it, answer the AXI write.")
    A("            if (mst != M_IDLE) begin")
    A("                mem_tmo <= mem_tmo + 11'd1;")
    A(f"                if (mem_tmo == 11'h{HOST_TIMEOUT:03X}) begin")
    A(f"                    mem_timeout <= 1'b1; mem_hreq <= {nm}'b0; mst <= M_IDLE; mem_busy <= 1'b0; mem_resp <= 1'b1;")
    A("                end")
    A("            end")
    A("        end")
    A("    end")
    A("")
    return L


def void_completion_lines(ctl_out):
    """A VOID kernel's completion: the bench's o_req is the join of every control result.

    A kernel with no out0 (most of Dynamatic's array kernels) has nothing for the batch FSM to wait on, so the call's
    completion is made from its control results, as Dynamatic's own testbench joins all of a kernel's outputs: `end`
    and every memory's <m>_end (its mem_controller's memEnd).  The join drives o_req_pl and takes o_ack_pl, so the
    batch FSM, the latency counters and the acknowledge's return to zero are exactly as for out0; ODATA reads 0 and
    the result is the arrays, read back through the host port after the batch (bench_gate.sh GATE_MEMEXP).

    Why memEnd is the completion: for a memory with a store, bdc orders its ctrlEnd after every store of the call
    (research/data/suite/stores.md), and memEnd waits for ctrlEnd, so a run is not complete -- and the host does not
    read an array back, nor start the next run -- before the last store has reached the RAM.

    Why `end` goes through a link first: in bdc's lowering `end` is the start token passed straight through (the
    start fork's other outputs start the loop).  A join input acknowledges only when the call is complete, and a
    fork acknowledges only when all its outputs have, so `end` straight into the join would hold the start fork's
    request high until the call ends -- its other outputs could not return to zero, and a loop header waiting on that
    deadlocks (stores.md measured exactly this inside the kernel).  A one-token bd_link acknowledges the token at once
    and holds it for the join: the bd_link + bd_join pair bdc itself builds for a memory's memStart (emit.py
    _op_mem_controller).  memEnds need no link: each is made from the exit block's single control token, so all of
    them can arrive while the join holds the others."""
    L = []
    A = L.append
    A("    // ---- a VOID kernel's completion (gen_bench.py void_completion_lines) ---------------------------------")
    A("    // No out0: the result is the arrays, read back after the batch.  A call is complete when every control")
    A("    // result has arrived -- `end` and each memory's <m>_end (memEnd: after every store of the call, bdc's store")
    A("    // lowering) -- as Dynamatic's testbench joins all outputs.  The join is o_req; ODATA reads 0.  `end` is the")
    A("    // start token passed through, so it is held in a link (acknowledged at once): joined directly, it would")
    A("    // hold the start fork's request high, and with it the loop, until the call ended.")
    A("    wire end_hold_req, end_hold_ack;")
    A("    bd_link #(.W(1)) uend_hold (")
    A("        .rst(rst_pl),")
    A("        .req_in(p_end_req), .ack_in(p_end_ack), .data_in(1'b0),")
    A("        .req_out(end_hold_req), .ack_out(end_hold_ack), .data_out());")
    reqs = ", ".join([f"{portname(c.name)}_req" for c in reversed(ctl_out)] + ["end_hold_req"])
    acks = ", ".join([f"{portname(c.name)}_ack" for c in reversed(ctl_out)] + ["end_hold_ack"])
    A(f"    bd_join #(.N({len(ctl_out) + 1})) ucomplete (")
    A(f"        .rst(rst_pl), .req_in({{{reqs}}}),")
    A(f"        .ack_out({{{acks}}}),")
    A("        .req(o_req_pl), .ack(o_ack_pl));")
    A("    assign o_data_pl = 32'b0;")
    return L


def words_for(width):
    # A scalar narrower than 32 bits (Dynamatic's test_stdint: an int8_t) takes one word's low bits, as an array
    # element narrower than 32 bits does (research/data/suite/bench/README.md); the oracle casts the word to the C type.
    if 0 < width < 32:
        return 1
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
    # A memref parses as a width-0 NON-control channel (bdc/hs/parse.py), so it must be taken out before the data
    # args are counted: it has no _req/_ack/_data port on the kernel (bdc/emit.py) and no operand word here.
    mems = [a for a in func.args if a.raw.startswith("memref")]
    data_args = [a for a in func.args if not a.is_control and not a.raw.startswith("memref")]
    total_words = sum(words_for(a.width) for a in data_args)
    if total_words > MAX_WORDS:
        raise SystemExit(f"{kernel}: needs {total_words} operand words, this generator's fixed "
                          f"register file only has {MAX_WORDS} -- widen MAX_WORDS and the "
                          f"register map before using this kernel, do not silently truncate it")
    if func.name != kernel:
        raise SystemExit(f"{mlir}: handshake.func @{func.name} does not match kernel name "
                          f"{kernel!r} passed on the command line")
    # Control arguments other than `start` (a memory's memStart, `<m>_start`) are offered with every call, like
    # start; control results other than `end` (a memory's memEnd, `<m>_end`) are taken by a sink, like end.
    ctl_in = [a for a in func.args if a.is_control and a.name != "start"]
    ctl_out = [r for r in func.results if r.is_control and r.name != "end"]
    if [a.name for a in func.args if a.is_control and a.name == "start"] != ["start"] or \
            [r.name for r in func.results if r.is_control and r.name == "end"] != ["end"]:
        raise SystemExit(f"{mlir}: @{func.name} needs exactly one `start` argument and one `end` result")
    data_res = [r for r in func.results if not r.is_control]
    # One result, out0, of at most 32 bits.  Narrower is ZERO-extended into ODATA (emit() below): the handshake type
    # is signless, so the C type's signedness is not known here, and an undriven upper half is not a value.  The
    # oracle masks the C's result to the same width (research/tools/suite/oracle_mem.sh).  Wider (an i64 result)
    # would need a second ODATA word through result_hold/SIG/the mismatch latch: refused, not truncated.
    # Or none at all: a VOID kernel (most of Dynamatic's array kernels), whose result is its arrays.  Its call
    # completes on its control results instead (emit(), "a void kernel's completion"); it needs a memory (checked
    # below), or nothing it does could be seen.
    if data_res and ([r.name for r in data_res] != ["out0"] or not 1 <= data_res[0].width <= 32):
        raise SystemExit(f"{mlir}: @{func.name} returns {[(r.name, r.width) for r in data_res]}; the bench "
                         f"captures exactly one result, out0, of 1 to 32 bits")
    memspec = []
    for a in mems:
        m = re.fullmatch(r"memref<(\d+)x[iu](\d+)>", a.raw)
        if not m:
            raise SystemExit(f"{kernel}: memref argument {a.name!r} is {a.raw!r}, not memref<NxiW>")
        depth, dw = int(m.group(1)), int(m.group(2))
        if dw > 32:
            raise SystemExit(f"{kernel}: memref {a.name!r} has {dw}-bit elements; the host path moves one "
                             f"32-bit word per element -- elements wider than 32 bits are not supported")
        if (a.name + "_start") not in [c.name for c in ctl_in] or (a.name + "_end") not in [c.name for c in ctl_out]:
            raise SystemExit(f"{kernel}: memref {a.name!r} has no {a.name}_start argument / {a.name}_end result")
        # bdc/emit.py's own address width for this memref (_resolve_widths): the host port is that wide.
        memspec.append((a.name, depth, dw, max(1, (depth - 1).bit_length())))
    if len(memspec) > MAX_MEMS:
        raise SystemExit(f"{kernel}: {len(memspec)} memories; the host path addresses at most {MAX_MEMS}")
    if not data_res and not memspec:
        raise SystemExit(f"{mlir}: @{func.name} returns nothing and has no memory: the bench would have nothing to "
                         f"read (a void kernel's result is its arrays, read back through the host port)")
    # ow = out0's width; 0 marks a void kernel (emit())
    return data_args, memspec, ctl_in, ctl_out, (data_res[0].width if data_res else 0)


def emit(kernel, is_null, top_name):
    frontend_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "build", "frontend")
    data_args, mems, ctl_in, ctl_out, ow = load_signature(kernel, frontend_dir)
    nargs = len(data_args)
    restr = DOMAIN_RESTRICTIONS.get(kernel, {})
    # nw = operand words the kernel needs; the register file always has OP0/OP1, and OP2.. only when nw > 2.
    nw = sum(words_for(a.width) for a in data_args)
    nwr = max(2, nw)
    wide = nw > 2
    nm = len(mems)
    void = ow == 0   # no out0: the call completes on its control results (see "a void kernel's completion" below)
    if is_null and (mems or ctl_in or ctl_out):
        raise SystemExit(f"{kernel}: --null is not built for a kernel with memories or extra control channels "
                         f"(the null DUT would need a memory behind each host port)")

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
    if wide:
        P(f"// {nw} operand words: OP0, OP1 at 7'h02/7'h03, OP2..OP{nw - 1} at 7'h{OPX_BASE:02X}.. (gen_bench.py MAX_WORDS)")
    if mems:
        P(f"// {nm} memor{'y' if nm == 1 else 'ies'}, each behind a host port (bdc/emit.py --host-mem): "
          + ", ".join(f"{n}[{d}] i{w} (aw {aw})" for n, d, w, aw in mems))
    if void:
        P("// void: no out0 -- a call completes when `end` and every <m>_end have arrived; ODATA reads 0, the "
          "result is the arrays")
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
        P(f"    // The ONLY delay here is the bundling delay: out0_data is an XOR fold")
        P(f"    // of the joined operands, so out0_req must not reach the consumer")
        P(f"    // before that fold has settled. N=10 LUT1s is the first-phase estimate")
        P(f"    // for a 1-2 level fold; it is the one number in this module that a")
        P(f"    // post-PnR tightening pass may shorten.")
        P(f"    //")
        P(f"    // Everything else is a real 4-phase relay. An earlier version of this")
        P(f"    // file wrote")
        P(f"    //     bd_delay #(.N(6))  uack (.a(joined_req), .z(joined_ack));")
        P(f"    //     bd_delay #(.N(10)) uout (.a(joined_req), .z(out0_req));")
        P(f"    //     assign p_end_req = joined_req;")
        P(f"    // which FABRICATES the acknowledge out of a delay instead of waiting")
        P(f"    // for one, and never references out0_ack or p_end_ack at all. That is")
        P(f"    // not a 4-phase channel: joined_ack rose 4 delays BEFORE out0_req even")
        P(f"    // asserted, so the upstream released the operands while the output")
        P(f"    // transaction had not started, and out0_req then returned to zero on a")
        P(f"    // timer rather than on the consumer's acknowledge. It only ever worked")
        P(f"    // because this harness's consumer happens to be faster than the delay")
        P(f"    // -- a consumer one LUT slower would have dropped results silently.")
        P(f"    //")
        P(f"    // bd_fork is exactly this shape: broadcast the request to out0 and")
        P(f"    // p_end, rendezvous their acknowledges in a C-element tree, and hand")
        P(f"    // that back as the join's acknowledge. Now the null control obeys the")
        P(f"    // same protocol as every real kernel, which is the whole point of a")
        P(f"    // control: its latency is only subtractable from theirs if it pays the")
        P(f"    // same handshake, not a shorter one.")
        fold_terms = []
        for a in data_args:
            for w in range(words_for(a.width)):
                fold_terms.append(f"{a.name}_data[{w * 32 + 31}:{w * 32}]" if a.width >= 32
                                  else f"{{{32 - a.width}'b0, {a.name}_data}}")
        P(f"    assign out0_data = {' ^ '.join(fold_terms)};")
        P(f"    wire fork_req;")
        P(f"    bd_delay #(.N(10)) ubundle (.a(joined_req), .z(fork_req));")
        P(f"    bd_fork #(.N(2)) ufork (.rst(rst), .req(fork_req), .ack(joined_ack),")
        P(f"        .req_out({{p_end_req, out0_req}}), .ack_in({{p_end_ack, out0_ack}}));")
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
    if wide:
        P("    reg [31:0] " + ", ".join(f"op{k}" for k in range(2, nw)) +
          f";   // OP2..: 7'h{OPX_BASE:02X}.. (gen_bench.py MAX_WORDS)")
    P("    reg [31:0] n_runs, cycles, prep_cycles, lat_min, lat_max;")
    P("    reg        bctrl_start, bctrl_rst;")
    P("    reg [1:0]  bctrl_mode;                // 0=uniform 1=fixed 2=legacy-biased")
    P("    reg [31:0] last_op0, last_op1;")
    P("    reg [31:0] sig;")
    P("    // ---- the single point at which a run's RESULT is captured ----------")
    P("    // Every consumer of a result (SIG, the repeatability latch, and the")
    P("    // host's ODATA readback) reads THIS register, so they cannot disagree")
    P("    // about what the kernel returned.  They used to disagree: SIG/ODATA")
    P("    // read o_data_capture in S_NEXT (after the acknowledge) while the")
    P("    // mismatch latch read raw o_data_pl in S_WAIT_RES (at the completion")
    P("    // edge), and on isprime those two answers differ -- the mismatch path")
    P("    // saw the correct 0/1 and ODATA/SIG read 0x80000000 on every run.")
    P("    //")
    P("    // 4-phase bundled data says exactly one thing about when the result is")
    P("    // readable: it is valid from the moment o_req is high until the sender")
    P("    // sees o_ack and returns to zero.  So capture it INSIDE that window --")
    P("    // on the last edge before this harness asserts bench_o_ack.  Reading")
    P("    // after the acknowledge (what S_NEXT did) is outside the window and is")
    P("    // only correct for kernels whose output bus happens to keep holding.")
    P("    reg [31:0] result_hold;")
    P("    reg        hold_valid;      // a batch result has been captured")
    P("    reg        hold_fallback;   // sticky: see the res_wait timeout below")
    P("    reg [7:0]  res_wait;")
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
    P("    // ILLEGAL-STATE DETECTOR.  On silicon this bridge has been read, at a")
    P("    // hang, in a state the RTL below cannot produce: st == S_RTZ while")
    P("    // bench_o_ack == 0.  S_WAIT_RES sets bench_o_ack on its way into S_ACK,")
    P("    // and the ONLY clear is inside S_RTZ's own if-body, in the same breath")
    P("    // as st <= S_NEXT -- and runs_done was frozen, so S_NEXT never ran.")
    P("    // The two other writers (async reset, bctrl_rst) both also force st to")
    P("    // S_IDLE and zero runs_done/cycles, which read 28 and 142M.  So the pair")
    P("    // is unreachable in source, and the snapshot cannot say which edge made")
    P("    // it -- by the time a host polls, the evidence is 142M cycles old.")
    P("    //")
    P("    // st and bench_o_ack are SEPARATE flops with SEPARATE D/CE cones, each")
    P("    // independently recomputing S_RTZ's !o_req_s condition.  That is the one")
    P("    // structure that can leave them disagreeing, and these stickies are")
    P("    // built to tell that apart from the alternative (arriving in S_RTZ with")
    P("    // the ack already low) by recording the PREVIOUS cycle's st/bench_o_ack:")
    P("    //")
    P("    //   ill_prev_st == S_RTZ  and ill_prev_oack == 1 -> bench_o_ack dropped")
    P("    //        while st stayed put: the two cones DID diverge on one edge.")
    P("    //   ill_prev_st == S_ACK  and ill_prev_oack == 0 -> we entered S_RTZ")
    P("    //        already broken, so S_WAIT_RES's set never landed.")
    P("    //   anything else -> neither story; read the raw fields.")
    P("    reg        ill_sticky, ill_prev_oack, ill_oreqs, ill_sync0;")
    P("    reg [2:0]  ill_prev_st;")
    P("    reg [15:0] ill_run;")
    P("    reg [31:0] ill_cycles;")
    P("    reg [2:0]  st_d;")
    P("    reg        oack_d;")
    P("    // ILLEGAL-TRANSITION DETECTOR.  The pair sticky above only notices the")
    P("    // one corrupted code that happens to land on S_RTZ; the mechanism (a")
    P("    // multi-bit state register sampling an unsynchronised input) can just as")
    P("    // easily land on any other mix of the state it left and the state it was")
    P("    // heading for, and those go unseen.  This watches the TRANSITION instead,")
    P("    // so it catches every invalid code, and it is the regression gate for the")
    P("    // synchroniser: after that fix, it must never fire.")
    P("    reg        ill_tr_sticky;")
    P("    reg [2:0]  ill_tr_from, ill_tr_to;")
    P("    wire st_legal =")
    P("        (st == st_d)")
    P("            ? (st_d == S_IDLE || st_d == S_PREP || st_d == S_WAIT_ACK ||")
    P("               st_d == S_WAIT_RES || st_d == S_RTZ)")
    P("            : ((st_d == S_IDLE     && st == S_PREP)     ||")
    P("               (st_d == S_PREP     && st == S_ISSUE)    ||")
    P("               (st_d == S_ISSUE    && st == S_WAIT_ACK) ||")
    P("               (st_d == S_WAIT_ACK && st == S_WAIT_RES) ||")
    P("               (st_d == S_WAIT_RES && st == S_ACK)      ||")
    P("               (st_d == S_ACK      && st == S_RTZ)      ||")
    P("               (st_d == S_RTZ      && st == S_NEXT)     ||")
    P("               (st_d == S_NEXT     && (st == S_PREP || st == S_IDLE)));")
    P("    reg [31:0] lfsr;")
    P("    wire [31:0] lfsr_n1 = {lfsr[30:0], lfsr[31]^lfsr[21]^lfsr[1]^lfsr[0]};")
    P("    wire [31:0] lfsr_n2 = {lfsr_n1[30:0], lfsr_n1[31]^lfsr_n1[21]^lfsr_n1[1]^lfsr_n1[0]};")
    for k in range(3, nw + 1):   # UNIFORM draws word k from the LFSR advanced k times
        P(f"    wire [31:0] lfsr_n{k} = {{lfsr_n{k - 1}[30:0], lfsr_n{k - 1}[31]^lfsr_n{k - 1}[21]^"
          f"lfsr_n{k - 1}[1]^lfsr_n{k - 1}[0]}};")
    P("    reg [31:0] bench_op0, bench_op1;")
    if wide:
        P("    reg [31:0] " + ", ".join(f"bench_op{k}" for k in range(2, nw)) + ";")
    P("    reg        start_d;")
    P("    reg        have_ref;                  // FIXED-mode repeatability reference latched")
    P("")
    P("    wire       start_rise = bctrl_start & ~start_d;")
    P("")
    P("    // Bundled-data hazard note (see hw/gcd_bench.v): the FSM must not move")
    P("    // bench_op0/1 while a request is in flight.  S_PREP settles them first.")
    P("    wire [31:0] op0_to_core = bench_busy ? bench_op0 : op0;")
    P("    wire [31:0] op1_to_core = bench_busy ? bench_op1 : op1;")
    for k in range(2, nw):
        P(f"    wire [31:0] op{k}_to_core = bench_busy ? bench_op{k} : op{k};")
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
    P("    // just the single FSM state that consumes it. The null kernel used to")
    P("    // derive BOTH i_ack and o_req from the same trivial joined_req at")
    P("    // different bd_delay depths (N=6 vs N=10), so o_req rose and fell in well")
    P("    // under 1 ns -- entirely while st was still S_WAIT_ACK, one full clock edge")
    P("    // before the FSM even reached S_WAIT_RES to open a narrower window. That")
    P("    // null control is now a proper 4-phase relay and holds o_req as a level,")
    P("    // but the wide window stays: a fast REAL kernel can do the same thing, and")
    P("    // a poller that only works against slow kernels is not a poller. A version")
    P("    // gated on")
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
    P("    // ---- and now SYNCHRONISE them before the FSM is allowed to look ------")
    P("    // The latches above are set ASYNCHRONOUSLY, by raw combinational wires")
    P("    // out of a self-timed kernel that knows nothing about aclk.  Reading one")
    P("    // directly from the state machine is what caused the hang this harness")
    P("    // spent a day chasing: `st` is THREE flops, and gating a transition on an")
    P("    // input that can change inside their setup/hold window lets each flop")
    P("    // resolve independently, so the register lands on a code that is a")
    P("    // BITWISE MIX of the state it left and the state it was heading for.")
    P("    //")
    P("    // Caught on silicon by the 7'h16 sticky, five times in eight board runs,")
    P("    // always the same signature: S_WAIT_ACK (0b011) -> S_RTZ (0b110).  The")
    P("    // only transition out of S_WAIT_ACK is to S_WAIT_RES (0b100); 0b110 is")
    P("    // 011 and 100 mixed, bit2 new, bit1 old, bit0 new.  Landing in S_RTZ with")
    P("    // o_req_s already low makes S_RTZ fire at once, retiring a run that was")
    P("    // never acknowledged -- after which the FSM and the kernel disagree about")
    P("    // whose turn it is, and a while-ring kernel driven out of protocol wedges.")
    P("    //")
    P("    // Two flops, not one: the first may itself go metastable, the second is")
    P("    // what resolves it.  This is a SYNCHRONISER, not a matched delay -- it is")
    P("    // not sized, not tightened, and not on any bundled-data path.")
    P("    //")
    P("    // Cleared at S_ISSUE alongside the latches themselves.  Without that the")
    P("    // synchronised copy would still read the PREVIOUS transaction's 1 for two")
    P("    // cycles after the latch was cleared, and S_WAIT_ACK -- entered one cycle")
    P("    // after S_ISSUE -- would accept that stale high as this run's ack.")
    P("    reg [1:0] sync_i_ackl, sync_o_reql;")
    P("    wire i_ack_l_s = sync_i_ackl[1];")
    P("    wire o_req_l_s = sync_o_reql[1];")
    P("    always @(posedge aclk or negedge aresetn) begin")
    P("        if (!aresetn) begin")
    P("            sync_i_ackl <= 2\'b0; sync_o_reql <= 2\'b0;")
    P("        end else if (st == S_ISSUE) begin")
    P("            sync_i_ackl <= 2\'b0; sync_o_reql <= 2\'b0;")
    P("        end else begin")
    P("            sync_i_ackl <= {sync_i_ackl[0], i_ack_latched};")
    P("            sync_o_reql <= {sync_o_reql[0], o_req_latched};")
    P("        end")
    P("    end")
    P("")
    P("    // ---- 64-bucket log histogram of per-run latency (lat_ctr at completion) -")
    P("    // bucket = min(leading_one,15)*4 + 2 mantissa bits below the leading one.")
    P("    // ~19% resolution per bucket, 16 octaves -- see harness spec.")
    P("    //")
    P("    // This update is PIPELINED, and the reason is measured, not stylistic.")
    P("    // It used to be one statement in the completion cycle:")
    P("    //")
    P("    //     hist[bucket] <= hist[bucket] + 1;   // bucket combinational off lat_ctr")
    P("    //")
    P("    // which put a 32-bit leading-one priority encoder, a 64:1 F7/F8 read mux")
    P("    // over 2048 flops, and a 32-bit carry chain into a SINGLE clock.  nextpnr")
    P("    // measured that path end to end at ~30 ns -- pnr.log\'s critical path runs")
    P("    // lat_ctr[24] -> mux7/mux8 tree -> lead1[0] -> carry4 -> mux -- so the")
    P("    // bridge closed timing at 28-35 MHz across all twelve bench builds while")
    P("    // FCLK0 clocks it at 100 MHz.  Nothing announced this: the flow passes no")
    P("    // create_clock and no --freq, so nextpnr compared against its own 12 MHz")
    P("    // default and printed PASS.")
    P("    //")
    P("    // The failure was silent and partial, which is why it survived so long.")
    P("    // Small counts were exact and large ones were not: a FIXED batch of 1000")
    P("    // identical 5-cycle runs read back 1768 in its one bucket (n=1,2,3,10,100")
    P("    // were all exact), and gcd\'s 3000-run histogram summed to 2616.  Only the")
    P("    // percentiles were ever affected -- lat_min/lat_max/cycles/runs_done are")
    P("    // plain increments off short carry chains and were always right, which is")
    P("    // why min/max/mean/throughput never disagreed with themselves.")
    P("    //")
    P("    // Fix, in two parts.  (1) Latch the finished latency and do the encode and")
    P("    // the increment in the cycles AFTER completion: S_ACK/S_RTZ/S_NEXT/S_PREP")
    P("    // guarantee at least seven clocks before the next completion can land, so")
    P("    // each deep stage gets its own cycle and the value recorded is still the")
    P("    // exact lat_ctr of the run that finished.  (2) Encode 16 bits, not 32:")
    P("    // lead1 saturates at 15 anyway, so everything at or above 2**16 cycles")
    P("    // (655 us at 100 MHz -- no kernel here comes within three orders of it)")
    P("    // now lands in bucket 63 instead of dragging a 32-wide priority encoder")
    P("    // onto the path to express a distinction the buckets cannot hold.")
    P("    // 16 bits per bucket, not 32.  A bucket cannot exceed the batch size, and")
    P("    // run_all_bench.sh already refuses n > 65535 because BSTATUS reports")
    P("    // runs_done in a 16-bit field -- so the upper half of every counter was")
    P("    // unreachable by construction.  Paying for it cost 1024 flops and, worse,")
    P("    // doubled the width of the one net that could not be routed fast enough.")
    P("    // Saturating (rather than wrapping) keeps an over-long batch honest.")
    P("    reg [15:0] hist [0:63];")
    P("    integer hi;")
    P("    reg [31:0] lat_final;                  // stage A: latency of the run that just finished")
    P("    reg        hist_pend, hist_v2, hist_we; // one-cycle valids walking the pipe")
    P("    reg [5:0]  bucket_q, bucket_q2;")
    P("    reg [15:0] hist_rd;                    // stage C: hist[bucket_q] read -> reg")
    P("    reg        clearing, pending_start;")
    P("    reg [5:0]  clr_addr;")
    P("    wire       hist_clr_we = clearing;")
    P("    wire [15:0] hist_rd_comb = hist[bucket_q];   // async read; see the note below")
    P("    reg [3:0]  lead1;")
    P("    reg        found1;")
    P("    reg [1:0]  mant;")
    P("    reg [5:0]  bucket;")
    P("    wire       lat_hi = |lat_final[31:16];  // above the top octave: saturate")
    P("    always @(*) begin")
    P("        found1 = 1\'b0;")
    P("        lead1  = 4\'d0;")
    P("        for (hi = 15; hi >= 0; hi = hi - 1)")
    P("            if (!found1 && lat_final[hi]) begin lead1 = hi[3:0]; found1 = 1\'b1; end")
    P("        if (lead1 >= 4\'d2)")
    P("            mant = lat_final[lead1-1 -: 2];")
    P("        else if (lead1 == 4\'d1)")
    P("            mant = {lat_final[0], 1\'b0};")
    P("        else")
    P("            mant = 2\'b00;")
    P("        bucket = lat_hi ? 6\'d63 : (lead1 * 6\'d4 + {4\'b0, mant});")
    P("    end")
    P("")
    P("    // Stages B/C/D.  Deliberately NOT gated on bench_busy: a completion that")
    P("    // lands on the last run of a batch still has to finish walking the pipe.")
    P("    always @(posedge aclk or negedge aresetn) begin")
    P("        if (!aresetn) begin")
    P("            bucket_q <= 6\'b0; bucket_q2 <= 6\'b0;")
    P("            hist_rd  <= 16\'b0; hist_v2 <= 1\'b0; hist_we <= 1\'b0;")
    P("        end else begin")
    P("            // Stage valids must track the DATA, not the completion event: the")
    P("            // read mux is one stage behind the encoder, so hist_we is two")
    P("            // stages behind hist_pend and not one.")
    P("            bucket_q  <= bucket;            // B: encoder      -> reg")
    P("            hist_v2   <= hist_pend;")
    P("            bucket_q2 <= bucket_q;")
    P("            hist_rd   <= hist_rd_comb;      // C: read mux -> reg")
    P("            hist_we   <= hist_v2;           // D: read+1 written back, next cycle")
    P("        end")
    P("    end")
    P("")
    P("    // ---- hist[] has exactly ONE write port, on purpose ---------------------")
    P("    // Pipelining alone was not enough: splitting the encoder out took the")
    P("    // bridge from 33 to 84 MHz, and splitting the adder off the write demux")
    P("    // made it slightly WORSE (80.68).  The remaining path was not logic depth,")
    P("    // it was wire -- single hops of 2.6 ns and 4.3 ns fanning across the die,")
    P("    // because hist[] was 2048 scattered flops behind a 64:1 F7/F8 mux.  No")
    P("    // number of pipeline stages shortens a 4.3 ns net.")
    P("    //")
    P("    // It was flops because of the batch-start clear.  Zeroing all 64 entries")
    P("    // in one cycle asks for 64 write ports, which no RAM has, so yosys could")
    P("    // only ever infer registers.  Clearing sequentially instead (below) leaves")
    P("    // one synchronous write port and lets this become actual memory.")
    P("    // The read is a WIRE off the array, and the register that captures it")
    P("    // lives in the pipeline block above -- deliberately, and this cost a")
    P("    // board run to learn.  Writing it the obvious way,")
    P("    //")
    P("    //     always @(posedge aclk) begin")
    P("    //         hist_rd <= hist[bucket_q];        // synchronous read port")
    P("    //         ... hist[bucket_q2] <= hist_rd + 1;")
    P("    //     end")
    P("    //")
    P("    // makes yosys treat hist[] as a memory with a synchronous read port")
    P("    // rather than as an array of flops behind a mux, and the write ended up")
    P("    // on a different copy from the one feeding hist_rd.  Every increment then")
    P("    // read 0 and wrote 1: on the board, batches of n=1,2,3,10,100 ALL left")
    P("    // exactly 1 in the bucket.  iverilog cannot show this -- it simulates the")
    P("    // RTL, not the inference -- so sim passed the whole time.  Reading through")
    P("    // a plain wire keeps the same shape the original working code had (one")
    P("    // clocked writer, asynchronous readers) while still pipelining the mux.")
    P("    always @(posedge aclk) begin")
    P("        if (hist_clr_we)  hist[clr_addr]  <= 16\'b0;")
    P("        else if (hist_we && hist_rd != 16\'hFFFF)")
    P("                          hist[bucket_q2] <= hist_rd + 16\'d1;")
    P("    end")
    P("")
    P("    always @(posedge aclk or negedge aresetn) begin")
    P("        if (!aresetn) begin")
    P("            st <= S_IDLE; bench_busy <= 1'b0; bench_done <= 1'b0;")
    P("            bench_set_req <= 1'b0; bench_o_ack <= 1'b0;")
    P("            ill_sticky <= 1'b0; ill_prev_st <= 3'b0; ill_prev_oack <= 1'b0;")
    P("            ill_oreqs <= 1'b0; ill_sync0 <= 1'b0; ill_run <= 16'b0;")
    P("            ill_cycles <= 32'b0; st_d <= 3'b0; oack_d <= 1'b0;")
    P("            ill_tr_sticky <= 1'b0; ill_tr_from <= 3'b0; ill_tr_to <= 3'b0;")
    P("            runs_done <= 32'b0; lat_ctr <= 32'b0; prep_ctr <= 32'b0;")
    P("            cycles <= 32'b0; prep_cycles <= 32'b0;")
    P("            lat_min <= 32'hFFFFFFFF; lat_max <= 32'b0;")
    P("            lfsr <= 32'h1; bench_op0 <= 32'b0; bench_op1 <= 32'b0;")
    if wide:
        P("            " + " ".join(f"bench_op{k} <= 32'b0;" for k in range(2, nw)))
    P("            last_op0 <= 32'b0; last_op1 <= 32'b0; start_d <= 1'b0;")
    P("            sig <= 32'b0; mismatch_sticky <= 1'b0; mismatch_idx <= 32'b0;")
    P("            mismatch_val <= 32'b0; mismatch_ref <= 32'b0; have_ref <= 1'b0;")
    P("            result_hold <= 32'b0; hold_valid <= 1'b0; hold_fallback <= 1'b0;")
    P("            res_wait <= 8'b0;")
    P("            lat_final <= 32'b0; hist_pend <= 1'b0;")
    P("            clearing <= 1'b1; clr_addr <= 6'd0; pending_start <= 1'b0;")
    P("        end else begin")
    P("            start_d <= bctrl_start;")
    P("            bench_set_req <= 1'b0;")
    P("")
    P("            // One-cycle history, and the illegal-pair sticky.  Placed BEFORE")
    P("            // the bctrl_rst branch on purpose: bctrl_rst assigns ill_sticky")
    P("            // again below and the later non-blocking assignment wins, so a")
    P("            // batch reset always clears the detector even if the illegal")
    P("            // pair happens to be true on that very edge.  A sticky that only")
    P("            // ever cleared at power-on could never be trusted a second time.")
    P("            st_d   <= st;")
    P("            oack_d <= bench_o_ack;")
    P("            if (bench_busy && st == S_RTZ && !bench_o_ack && !ill_sticky) begin")
    P("                ill_sticky    <= 1'b1;")
    P("                ill_prev_st   <= st_d;")
    P("                ill_prev_oack <= oack_d;")
    P("                ill_oreqs     <= o_req_s;")
    P("                ill_sync0     <= sync_o_req[0];")
    P("                ill_run       <= runs_done[15:0];")
    P("                ill_cycles    <= cycles;")
    P("            end")
    P("            if (bench_busy && !st_legal && !ill_tr_sticky) begin")
    P("                ill_tr_sticky <= 1'b1;")
    P("                ill_tr_from   <= st_d;")
    P("                ill_tr_to     <= st;")
    P("            end")
    P("")
    P("            if (bctrl_rst) begin")
    P("                st <= S_IDLE; bench_busy <= 1'b0; bench_done <= 1'b0;")
    P("                bench_o_ack <= 1'b0; runs_done <= 32'b0; cycles <= 32'b0;")
    P("                ill_sticky <= 1'b0; ill_prev_st <= 3'b0; ill_prev_oack <= 1'b0;")
    P("                ill_oreqs <= 1'b0; ill_sync0 <= 1'b0; ill_run <= 16'b0;")
    P("                ill_cycles <= 32'b0;")
    P("                ill_tr_sticky <= 1'b0; ill_tr_from <= 3'b0; ill_tr_to <= 3'b0;")
    P("                prep_cycles <= 32'b0;")
    P("                lat_min <= 32'hFFFFFFFF; lat_max <= 32'b0;")
    P("                sig <= 32'b0; mismatch_sticky <= 1'b0; mismatch_idx <= 32'b0;")
    P("                mismatch_val <= 32'b0; mismatch_ref <= 32'b0; have_ref <= 1'b0;")
    P("                result_hold <= 32'b0; hold_valid <= 1'b0; hold_fallback <= 1'b0;")
    P("                res_wait <= 8'b0;")
    P("                lat_final <= 32'b0; hist_pend <= 1'b0;")
    P("                clearing <= 1'b1; clr_addr <= 6'd0; pending_start <= 1'b0;")
    P("            end else begin")
    P("                // CYCLES excludes S_PREP settling (measurement defect item in the")
    P("                // spec); PREP_CYCLES accumulates the same window separately so it")
    P("                // is reported, never silently dropped.")
    P("                if (bench_busy && st == S_PREP && prep_cycles != 32'hFFFFFFFF)")
    P("                    prep_cycles <= prep_cycles + 1;")
    P("                // ...and neither window bills the 64-cycle histogram scrub, which")
    P("                // runs with bench_busy already high but before the first request.")
    P("                if (bench_busy && st != S_PREP && st != S_IDLE && !clearing && cycles != 32'hFFFFFFFF)")
    P("                    cycles <= cycles + 1;")
    P("                if (st != S_IDLE && st != S_NEXT) lat_ctr <= lat_ctr + 1;")
    P("")
    P("                // hist_pend is a one-cycle handoff: default it low here so")
    P("                // S_WAIT_RES\'s set below (later in source order, so it wins) is")
    P("                // a pulse and not a level that would re-trigger the pipe.")
    P("                hist_pend <= 1'b0;")

    P("                case (st)")
    P("                    // hist[] must reset every batch, same as runs_done/lat_min/")
    P("                    // lat_max/sig -- otherwise back-to-back batches (the host does")
    P("                    // not issue BCTRL.bench_rst between them) silently accumulate")
    P("                    // into one histogram and the host reads a corrupted per-batch")
    P("                    // distribution.  Found via the sum(hist)==run_count check.")
    P("                    //")
    P("                    // The clear WALKS now, one entry per cycle, because a 64-wide")
    P("                    // parallel clear is what pinned hist[] into flops (see the")
    P("                    // single-write-port note above).  It runs AFTER start_rise, not")
    P("                    // before: the host reads the previous batch's histogram between")
    P("                    // batches, so zeroing early would erase the results it came for.")
    P("                    // 64 cycles once per batch, against thousands of runs, and the")
    P("                    // async kernel is not touched by any of it.")
    P("                    // start_rise is an EDGE, so it must be ACCEPTED whenever it")
    P("                    // arrives, including mid-scrub.  A first version made the")
    P("                    // scrub and the start mutually exclusive arms of one if/else,")
    P("                    // which silently DROPPED any start edge landing inside the")
    P("                    // 64-cycle reset scrub -- invisible over JTAG, where the host")
    P("                    // is thousands of cycles slower than the scrub, and a hard")
    P("                    // hang for tb_null_*_gen.v, whose AXI writes finish ~35 cycles")
    P("                    // after reset.  Arm first, scrub second: the arm can set")
    P("                    // pending_start during a scrub already in flight (which zeroes")
    P("                    // all 64 entries regardless of where the edge landed), and the")
    P("                    // third arm launches a batch whose scrub had already ended.")
    P("                    S_IDLE: begin")
    P("                        if (start_rise && n_runs != 32'b0) begin")
    P("                            bench_busy <= 1'b1; bench_done <= 1'b0;")
    P("                            runs_done  <= 32'b0; cycles <= 32'b0; prep_cycles <= 32'b0;")
    P("                            lat_min    <= 32'hFFFFFFFF; lat_max <= 32'b0;")
    P("                            sig <= 32'b0; mismatch_sticky <= 1'b0; have_ref <= 1'b0;")
    P("                            hold_valid <= 1'b0; hold_fallback <= 1'b0;")
    P("                            lfsr       <= (op0 == 32'b0) ? 32'h1 : op0;")
    P("                            // stay in S_IDLE until the scrub finishes")
    P("                            pending_start <= 1'b1;")
    P("                            if (!clearing) begin clearing <= 1'b1; clr_addr <= 6'd0; end")
    P("                        end")
    P("                        if (clearing && clr_addr == 6'd63) begin")
    P("                            clearing <= 1'b0;")
    P("                            if (pending_start) begin")
    P("                                pending_start <= 1'b0;")
    P("                                st <= S_PREP;")
    P("                            end")
    P("                        end else if (clearing) begin")
    P("                            clr_addr <= clr_addr + 6'd1;")
    P("                        end else if (pending_start) begin")
    P("                            // armed on the very cycle the scrub ended: launch next")
    P("                            pending_start <= 1'b0;")
    P("                            st <= S_PREP;")
    P("                        end")
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
    fixed = apply_domain_masks(kernel, data_args, [f"op{k}" for k in range(nwr)])
    if not wide:
        P(f"                                2'd1: begin bench_op0 <= {fixed[0]}; bench_op1 <= {fixed[1]}; end")
    else:
        P("                                2'd1: begin")
        for k in range(nw):
            P(f"                                    bench_op{k} <= {fixed[k]};")
        P("                                end")
    # LEGACY is gcd's old biased draw for words 0 and 1; any further word is run as written (FIXED).
    legacy = apply_domain_masks(
        kernel, data_args,
        ["({8'b0, lfsr[23:0]} | 32'd1)",
         "({8'b0, {lfsr[11:0], lfsr[23:12]}} | 32'd1)"] + [f"op{k}" for k in range(2, nw)])
    P("                                2'd2: begin")
    for k in range(nwr):
        P(f"                                    bench_op{k} <= {legacy[k]};")
    P("                                    lfsr <= {lfsr[30:0], lfsr[31]^lfsr[21]^lfsr[1]^lfsr[0]};")
    P("                                end")
    uni = apply_domain_masks(kernel, data_args, ["lfsr"] + [f"lfsr_n{k}" for k in range(1, nwr)])
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
    for k in range(nwr):
        P(f"                                    bench_op{k} <= {uni[k]};")
    P(f"                                    lfsr <= lfsr_n{nwr};")
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
    P("                    // Synchronised copies, never the async latches themselves.")
    P("                    // OR, not just i_ack: waiting for the input acknowledge BEFORE")
    P("                    // offering an output acknowledge assumes the kernel is")
    P("                    // decoupled -- that some storage stage lets it retire the input")
    P("                    // channel before its output channel is consumed. Every real")
    P("                    // kernel here is (they all carry bd_link/bd_pipe), so for them")
    P("                    // i_ack_l_s is what fires and nothing about this changes. A")
    P("                    // FULLY COUPLED kernel -- the null control is one: a join, a")
    P("                    // bundling delay and a fork, no storage anywhere -- cannot")
    P("                    // acknowledge its input until its output has been taken, and")
    P("                    // against the old sequential form that is a deadlock, not a")
    P("                    // slow kernel: i_ack waits on o_ack, o_ack waits on S_WAIT_RES,")
    P("                    // S_WAIT_RES waits on i_ack. Coupled is legal 4-phase, so the")
    P("                    // poller accepts whichever edge arrives first.")
    P("                    // Nothing is lost by not waiting here: the input channel's")
    P("                    // return to zero is not this FSM's job at all -- req_clr above")
    P("                    // asynchronously drops i_req the instant i_ack rises, whenever")
    P("                    // that happens.")
    P("                    S_WAIT_ACK: if (i_ack_l_s || o_req_l_s) st <= S_WAIT_RES;")
    P("")
    P("                    // Wait for the LEVEL o_req_s as well as the edge latch")
    P("                    // o_req_l_s.  o_req_latched is set ASYNCHRONOUSLY by any")
    P("                    // rise on o_req, so it also fires on a transient that")
    P("                    // never becomes a completion; o_req_s is a 2-flop")
    P("                    // synchronised sample of the level, which a transient")
    P("                    // shorter than a clock does not survive.  For a genuine")
    P("                    // completion both are the same 2-flop delay off the same")
    P("                    // rise, so this costs 0-1 cycles per run; res_wait bounds")
    P("                    // the case where they disagree so a harness that has been")
    P("                    // made stricter can never turn a wrong answer into a hang.")
    P("                    S_WAIT_RES: if (o_req_l_s && (o_req_s || res_wait == 8'hFF)) begin")
    P("                        res_wait <= 8'b0;")
    P("                        if (!o_req_s) hold_fallback <= 1'b1;")
    P("                        last_op0 <= bench_op0; last_op1 <= bench_op1;")
    P("                        if (lat_ctr < lat_min) lat_min <= lat_ctr;")
    P("                        if (lat_ctr > lat_max) lat_max <= lat_ctr;")
    P("                        lat_final <= lat_ctr; hist_pend <= 1'b1;   // hand off to the pipe")
    P("                        // THE capture.  bench_o_ack is still low on this edge")
    P("                        // (it is assigned below, so it rises after it), which is")
    P("                        // what makes o_data_pl guaranteed-valid here.")
    P("                        result_hold <= o_data_pl; hold_valid <= 1'b1;")
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
    P("                        // The latch itself now lives in S_NEXT and compares")
    P("                        // result_hold, so it and SIG are two readings of ONE")
    P("                        // captured value rather than two independent samples of a")
    P("                        // moving bus.  Its old note here -- 'still reads o_data_pl")
    P("                        // directly, same class of risk as SIG had, flagged for")
    P("                        // whoever looks at this next' -- is that fix.")
    P("                        bench_o_ack <= 1'b1;")
    P("                        st <= S_ACK;")
    P("                    end else if (o_req_l_s) begin")
    P("                        res_wait <= res_wait + 8'd1;")
    P("                    end")
    P("")
    P("                    S_ACK: st <= S_RTZ;")
    P("                    S_RTZ: if (!o_req_s) begin bench_o_ack <= 1'b0; st <= S_NEXT; end")
    P("                    S_NEXT: begin")
    P("                        // signature: rotate-left-1 then XOR in this run's result --")
    P("                        // cheap (one 32-bit XOR+rotate), and the host replays the")
    P("                        // identical LFSR sequence in software to compute the same")
    P("                        // value from the seed alone.")
    P("                        //")
    P("                        // Folded HERE, in a state that runs exactly once per run,")
    P("                        // but from result_hold -- captured back in S_WAIT_RES while")
    P("                        // the kernel still owned the bus.  This used to read")
    P("                        // o_data_capture, a free-running mirror of o_data_pl, on the")
    P("                        // theory that a later read is a safer read.  It is not: by")
    P("                        // S_NEXT this harness has already acknowledged, so the")
    P("                        // sender is free to return to zero and drop the data, and on")
    P("                        // isprime it does -- ODATA and SIG read 0x80000000 every run")
    P("                        // while the kernel was returning the correct 0/1 all along.")
    P("                        // Late is not safe; INSIDE THE VALID WINDOW is safe.")
    P("                        sig <= {sig[30:0], sig[31]} ^ result_hold;")
    P("                        // Repeatability latch: meaningful in FIXED mode, where every")
    P("                        // run's operands are identical, so a correct deterministic")
    P("                        // circuit must return the identical result every time.  Any")
    P("                        // divergence is latched (sticky) with the failing run's index")
    P("                        // and observed value, against the run-0 reference.  runs_done")
    P("                        // is incremented below by a non-blocking assignment, so")
    P("                        // mismatch_idx gets THIS run's index, not the next one's.")
    P("                        if (bctrl_mode == 2'd1) begin")
    P("                            if (!have_ref) begin")
    P("                                have_ref <= 1'b1; mismatch_ref <= result_hold;")
    P("                            end else if (!mismatch_sticky && result_hold != mismatch_ref) begin")
    P("                                mismatch_sticky <= 1'b1;")
    P("                                mismatch_idx <= runs_done;")
    P("                                mismatch_val <= result_hold;")
    P("                            end")
    P("                        end")
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
    if mems:
        for line in host_mem_lines(mems):
            P(line)
    P("    // ---- AXI slave ----------------------------------------------------------")
    P("    always @(posedge aclk or negedge aresetn) begin")
    P("        if (!aresetn) begin")
    P("            axi_awready <= 1'b0; axi_wready <= 1'b0; axi_bvalid <= 1'b0;")
    P("            axi_arready <= 1'b0; axi_rvalid <= 1'b0;")
    P("            axi_bid <= 12'b0;    axi_rid <= 12'b0;   aw_en <= 1'b1;")
    P("            ctrl_i_req <= 1'b0;  ctrl_o_ack <= 1'b0; ctrl_rst <= 1'b1;")
    P("            op0 <= 32'b0; op1 <= 32'b0;")
    if wide:
        P("            " + " ".join(f"op{k} <= 32'b0;" for k in range(2, nw)))
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
    for k in range(2, nw):
        P(f"                    7'h{OPX_BASE + k - 2:02X}: op{k} <= wdata;")
    P("                    7'h5: n_runs    <= wdata;")
    P("                    7'h14: run_gap  <= wdata;   // inter-run gap, aclk cycles")
    P("                    7'h8: begin bctrl_start <= wdata[0]; bctrl_rst <= wdata[1]; bctrl_mode <= wdata[3:2]; end")
    P("                    default: ;")
    P("                endcase")
    P("            end")
    P("")
    if not mems:
        P("            if (do_write && ~axi_bvalid) axi_bvalid <= 1'b1;")
        P("            else if (bready && axi_bvalid) axi_bvalid <= 1'b0;")
    else:
        P("            // A MEMWDATA / MEMCMD write that starts a host access is answered when the access is over")
        P("            // (mem_resp), not now: the response is the host's flow control, and aw_en keeps the next")
        P("            // write out until it has been taken.  Every other write is answered as before.")
        P("            if (do_write && ~axi_bvalid && !mem_start) axi_bvalid <= 1'b1;")
        P("            else if (mem_resp && ~axi_bvalid) axi_bvalid <= 1'b1;")
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
    P("            // ODATA.  Inside/after a batch this is result_hold, the value")
    P("            // captured while the kernel still owned the bus; before any batch")
    P("            // has run (the manual 4-phase smoke path, where this FSM is idle")
    P("            // and never captures anything) it is o_data_capture, the")
    P("            // free-running mirror, which is the only thing there is to read")
    P("            // when the host is driving the handshake by hand.")
    P("            7'h04: rdata_r = hold_valid ? result_hold : o_data_capture;")
    P("            7'h05: rdata_r = n_runs;")
    P("            7'h14: rdata_r = run_gap;")
    P("            // 7'h15 -- the batch FSM's own state and the RAW handshake wires.")
    P("            //")
    P("            // Batches deadlock intermittently (~50%) at a random run index.")
    P("            // Until now the parked state had to be INFERRED from o_req_s, the")
    P("            // 2-flop SYNCHRONIZED view: o_req_s=1 was read as S_RTZ, o_req_s=0")
    P("            // as S_WAIT_RES. That inference is exactly what should not be")
    P("            // trusted here, because the synchronizer is itself a suspect --")
    P("            // and both values have now been observed on different hangs, so")
    P("            // one bit was being asked to name two different failures.")
    P("            //")
    P("            // st is the state directly. The rest are the UNSYNCHRONIZED wires")
    P("            // as the kernel actually drives them, which is sound to read here")
    P("            // precisely BECAUSE the thing being read is stuck: a parked FSM is")
    P("            // static, so there is no edge for a sampling race to fall into.")
    P("            // On a moving batch these bits are racy and mean nothing -- read")
    P("            // them only after a hang has been confirmed by frozen runs_done.")
    P("            //")
    P("            // req_core/o_req_latched/i_ack_latched are the async-edge flops")
    P("            // that gen_bench.py's own comment says exist to 'work around a")
    P("            // hang'. If one of them disagrees with the raw wire beside it,")
    P("            // that band-aid is the bug rather than the kernel.")
    P("            // [10] i_ack_l_s [11] o_req_l_s -- the SYNCHRONISED copies the")
    P("            // FSM actually reads, next to the raw latches, so a trace can")
    P("            // show the two agreeing (or not).")
    P("            7'h15: rdata_r = {20'b0, o_req_l_s, i_ack_l_s,")
    P("                              o_req_latched, i_ack_latched, req_core,")
    P("                              o_req_pl, i_ack_pl, bench_o_ack, bench_set_req, st};")
    P("            // 7'h16 -- the illegal-pair sticky and its one-cycle history.")
    P("            // Cleared by bctrl_rst, so the host can prove it reads 0 before")
    P("            // a batch and only then believe a 1 after one.")
    P("            //   [2:0] ill_prev_st  [3] ill_sticky  [4] ill_prev_oack")
    P("            //   [5] ill_oreqs (o_req_s)  [6] ill_sync0 (sync_o_req[0])")
    P("            //   [31:16] ill_run")
    P("            //   [7] ill_tr_sticky  [10:8] ill_tr_from  [13:11] ill_tr_to")
    P("            7'h16: rdata_r = {ill_run, 2'b0, ill_tr_to, ill_tr_from,")
    P("                              ill_tr_sticky, ill_sync0, ill_oreqs,")
    P("                              ill_prev_oack, ill_sticky, ill_prev_st};")
    P("            7'h17: rdata_r = ill_cycles;")
    P("            7'h06: rdata_r = cycles;")
    P("            7'h07: rdata_r = prep_cycles;")
    P("            7'h08: rdata_r = {28'b0, bctrl_mode, bctrl_rst, bctrl_start};")
    P("            7'h09: rdata_r = {runs_done[15:0], 14'b0, bench_done, bench_busy};")
    P("            7'h0A: rdata_r = lat_min;")
    P("            7'h0B: rdata_r = lat_max;")
    P("            7'h0C: rdata_r = last_op0;")
    P("            7'h0D: rdata_r = last_op1;")
    P("            7'h0E: rdata_r = sig;")
    P("            //   [0] mismatch_sticky  [1] hold_valid  [2] hold_fallback")
    P("            // hold_fallback set means S_WAIT_RES timed out waiting for the")
    P("            // o_req LEVEL after the async edge latch had already fired, and")
    P("            // captured anyway -- the result is then no better founded than the")
    P("            // pre-2026-08-24 behaviour, so do not trust a SIG from that batch.")
    P("            7'h0F: rdata_r = {29'b0, hold_fallback, hold_valid, mismatch_sticky};")
    P("            7'h10: rdata_r = mismatch_idx;")
    P("            7'h11: rdata_r = mismatch_val;")
    P("            7'h12: rdata_r = mismatch_ref;")
    P(f"            7'h13: rdata_r = {{16'd{nargs}, 8'd{data_args[0].width if data_args else 0}, "
      f"8'd{data_args[-1].width if data_args else 0}}}; // {{nargs, arg0_width, argN_width}} metadata")
    P("            // zero-extended: the bucket is 16 bits wide, the register is 32")
    P("            7'b1zzzzzz: rdata_r = {16'b0, hist[axi_araddr[5:0]]};  // 0x40-0x7F -> hist[0..63]")
    for k in range(2, nw):
        P(f"            7'h{OPX_BASE + k - 2:02X}: rdata_r = op{k};")
    if mems:
        P(f"            7'h{MEM_ADDR:02X}: rdata_r = {{8'b0, mem_sel, mem_idx}};   // MEMADDR")
        P(f"            7'h{MEM_WDATA:02X}: rdata_r = mem_rd;")
        P(f"            7'h{MEM_STAT:02X}: rdata_r = {{mem_count, 13'b0, mem_timeout, mem_refused, mem_busy}};   // MEMSTAT")
        P(f"            7'h{MEM_RDATA:02X}: rdata_r = mem_rd;                     // MEMRDATA")
        for m, (name, depth, dw, aw) in enumerate(mems):
            P(f"            7'h{MEMINFO_BASE + m:02X}: rdata_r = {{16'd{depth}, 8'd{dw}, 8'd{aw}}};   // MEMINFO[{m}]: {name}")
    if wide or mems:
        P(f"            7'h{LAYOUT:02X}: rdata_r = {{8'd{nm}, 8'd{nw}, 16'h{LAYOUT_MAGIC:04X}}};   // LAYOUT {{nmem, nwords, magic}}")
    P("            default: rdata_r = 32'b0;")
    P("        endcase")
    P("    end")
    P("    assign rdata = rdata_r;")
    P("")
    P("    // ---- the kernel and its environment --------------------------------------")
    # Fork outputs: the data args in signature order, then any other control argument (a memory's <m>_start: its
    # mem_controller's memStart, one token per call like start), then start.  No extra controls -> as before.
    n_fork = nargs + len(ctl_in) + 1
    fork_ack_list = ", ".join(["start_ack"] + [portname(c.name) + "_ack" for c in reversed(ctl_in)]
                              + [a.name + "_ack" for a in reversed(data_args)])
    P(f"    wire [{n_fork - 1}:0] in_req;")
    P(f"    wire start_ack;")
    for a in data_args:
        P(f"    wire {a.name}_ack;")
    for c in ctl_in:
        P(f"    wire {portname(c.name)}_ack;")
    P("    wire p_end_req, p_end_ack;")
    for c in ctl_out:
        P(f"    wire {portname(c.name)}_req, {portname(c.name)}_ack;")
    P("")
    P(f"    bd_fork #(.N({n_fork})) ufork (")
    P(f"        .rst(rst_pl), .req(i_req_pl), .ack(i_ack_pl),")
    P(f"        .req_out(in_req), .ack_in({{{fork_ack_list}}}));")
    P("")
    if void:
        for line in void_completion_lines(ctl_out):
            P(line)
    else:
        P("    bd_delay #(.N(2)) upsnk (.a(p_end_req), .z(p_end_ack));")
        if ow < 32 and not is_null:   # out0 is narrower than ODATA: zero above it, stated (see load_signature)
            P(f"    assign o_data_pl[31:{ow}] = {32 - ow}'b0;   // out0 is i{ow}: ODATA holds it zero-extended")
        for c in ctl_out:   # a memory's <m>_end (memEnd) is taken like end
            P(f"    bd_delay #(.N(2)) u{portname(c.name)}_snk (.a({portname(c.name)}_req), .z({portname(c.name)}_ack));")
    P("")
    # ---- per-instance matched-delay overrides ------------------------------
    # The kernel takes one `parameter DELAY_<INST>` per delay-bearing cell and,
    # until now, this bench instantiated it with none of them -- so every chain
    # was built at bdc/emit.py's UNMEASURED estimate and verify/tighten.py had
    # nothing to attach its per-route proposals to.  Measured cost of that gap
    # on xorshift: chains built 122.2 ns where the route needs 76.0, and with
    # region fusion on, 122.7 ns where the route needs 30.2.  Fusion cut the
    # requirement by 2.5x and moved the board by 3%, because nothing shortened
    # the line it had just made shortenable.
    #
    # Spelling matches verify/tighten.py's macro(): full instance path, non-
    # alphanumerics to underscores, uppercased -- so udut.uxori0 inside bridge_i
    # is BD_SZ_BRIDGE_I_UDUT_UXORI0, which is the name tighten.py --emit writes.
    # Defaults are the kernel's own, so a bench built without a sizes file is
    # byte-for-byte the circuit it was before.
    dut_delays = kernel_delay_params(dut_module)
    for inst, dflt in dut_delays:
        m = "BD_SZ_BRIDGE_I_UDUT_" + inst.upper()
        P("`ifndef " + m)
        P(" `define " + m + " " + str(dflt))
        P("`endif")
    if dut_delays:
        P("")
        P(f"    {dut_module} #(")
        P(",\n".join(
            "        .DELAY_" + i.upper() + "(`BD_SZ_BRIDGE_I_UDUT_" + i.upper() + ")"
            for i, _ in dut_delays))
        P("    ) udut (")
    else:
        P(f"    {dut_module} udut (")
    P(f"        .rst       (rst_pl),")
    # Word wiring: for our 6 kernels nargs<=2 and each arg maps to a
    # contiguous, word-aligned slice of {op1_to_core,op0_to_core}.
    word_idx = 0
    core_exprs = []
    for a in data_args:
        nw = words_for(a.width)
        lo, hi = word_idx, word_idx + nw - 1
        if nw == 1 and a.width < 32:
            expr = f"op{lo}_to_core[{a.width - 1}:0]"   # a narrow scalar: the word's low bits (words_for)
        elif nw == 1:
            expr = f"op{lo}_to_core"
        else:
            expr = "{" + ", ".join(f"op{w}_to_core" for w in range(hi, lo - 1, -1)) + "}"
        core_exprs.append((a, expr))
        word_idx += nw
    for i, (a, expr) in enumerate(core_exprs):
        P(f"        .{a.name}_req  (in_req[{i}]), .{a.name}_ack  ({a.name}_ack), .{a.name}_data ({expr}),")
    for k, c in enumerate(ctl_in):
        P(f"        .{portname(c.name)}_req (in_req[{nargs + k}]), .{portname(c.name)}_ack ({portname(c.name)}_ack),")
    P(f"        .start_req (in_req[{nargs + len(ctl_in)}]), .start_ack (start_ack),")
    if void:
        pass   # no out0 port: o_req_pl / o_ack_pl / o_data_pl are the completion join's (void_completion_lines)
    elif ow < 32 and not is_null:
        P(f"        .out0_req  (o_req_pl),  .out0_ack  (o_ack_pl),  .out0_data (o_data_pl[{ow - 1}:0]),")
    else:
        P(f"        .out0_req  (o_req_pl),  .out0_ack  (o_ack_pl),  .out0_data (o_data_pl),")
    tail = [f"        .p_end_req (p_end_req), .p_end_ack (p_end_ack),"]
    for c in ctl_out:
        tail.append(f"        .{portname(c.name)}_req ({portname(c.name)}_req), "
                    f".{portname(c.name)}_ack ({portname(c.name)}_ack),")
    for m, (name, depth, dw, aw) in enumerate(mems):
        h = portname(name) + "_host"
        tail.append(f"        .{h}_req ({'mem_hreq' if nm == 1 else f'mem_hreq[{m}]'}), .{h}_ack (mem_hack{m}), "
                    f".{h}_addr (mem_idx[{aw - 1}:0]),")
        tail.append(f"        .{h}_wdata (mem_wd[{dw - 1}:0]), .{h}_we (mem_we), .{h}_rdata (mem_hrd{m}),")
    tail[-1] = tail[-1][:-1] + ");"
    for line in tail:
        P(line)
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


def apply_domain_masks(kernel, data_args, raws):
    """Given the UNMASKED Verilog expressions that would be drawn into
    bench_op0, bench_op1, ... this cycle (raws, one per operand word -- e.g.
    'lfsr'/'lfsr_n1' for UNIFORM, 'op0'/'op1' for FIXED), return the MASKED
    expressions that should actually be assigned, per the kernel's
    DOMAIN_RESTRICTIONS, as a list of the same length.

    Masking is applied to the raw expression INLINE, in the same
    non-blocking assignment that draws the word -- never as a later,
    separate assignment to the same reg (see the S_PREP comment in emit()
    for why that reads stale data under Verilog's NBA semantics).
    """
    restr = DOMAIN_RESTRICTIONS.get(kernel, {})
    raw = dict(enumerate(raws))
    masked = dict(raw)
    word_idx = 0
    for a in data_args:
        nw = words_for(a.width)
        lo, hi = word_idx, word_idx + nw - 1
        rule = restr.get(a.name)
        if rule is not None:
            if rule["kind"] == "positive_nonzero":
                # 0x1FFFFFFF, not 0x7FFFFFFF.  Clearing the sign bit alone is
                # NOT enough for collatz: the step is 3n+1 in signed int, which
                # overflows for any n > (INT_MAX-1)/3 = 715827882, and the
                # wrapped trajectory can enter a cycle that never reaches 1 --
                # so the kernel hangs, correctly, waiting for a result the
                # algorithm was never going to produce.  Same shape as gcd's
                # note below, and measured the same way rather than guessed:
                # on the board, collatz(2863311530 & 0x7FFFFFFF) = 715827882
                # terminates in 248 cycles, where 3n+1 is exactly INT_MAX, and
                # collatz(2882400001 & 0x7FFFFFFF) = 734916353 hangs, where it
                # is INT_MAX+57125413.  The boundary is exactly where the
                # arithmetic says it is.
                #
                # This is what hung the UNIFORM sweep at 0/3000 (collatz) and
                # 4/3000 (collatz64) while FIXED mode ran 200/200 -- FIXED
                # drives 48, which is nowhere near the bound.
                #
                # ...and bounding the START value is not sufficient either,
                # which is the second thing the board taught here.  Masking to
                # 0x1FFFFFFF (every start below (INT_MAX-1)/3) still hung, just
                # later: 9/3000 instead of 0/3000.  The overflow condition
                # applies to EVERY value on the trajectory, and Collatz climbs
                # well above its seed before it descends -- n=60975 peaks at
                # 593,279,152, nearly four orders above itself.
                #
                # So the mask is per-kernel and computed from the peak, not the
                # seed: exhaustively for int32 (all n <= 0xFFFF), by sampling
                # for int64.  See DOMAIN_RESTRICTIONS for both numbers.
                m = rule.get("mask", "32'h7FFFFFFF")
                masked[hi] = f"(({raw[hi]}) & {m})"
                if lo == hi:
                    masked[lo] = f"((({raw[lo]}) & {m}) == 32'h0 ? 32'h1 : (({raw[lo]}) & {m}))"
                else:
                    zero_check = " && ".join(f"(({raw[w]}) == 32'h0)" for w in range(lo, hi))
                    masked[lo] = (f"(({zero_check} && (({raw[hi]}) & {m}) == 32'h0) "
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
    return [masked[k] for k in range(len(raws))]


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
