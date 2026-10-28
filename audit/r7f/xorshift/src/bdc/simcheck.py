#!/usr/bin/env python3
"""The missing gate: does an emitted kernel COMPUTE THE RIGHT ANSWER.

bdc/test_compute.py checks arithmetic UNITS against Verilog's own operators.
cells/flow.sh checks that a design packs, places and routes.
cells/verify/tighten.py checks that matched delays are long enough.

None of those runs the emitted DATAFLOW GRAPH and looks at what comes out.
This does: it takes one emitted kernel module (bdc_<name>, from
bdc/emit.py's `generate(..., top=False)`), drives its argument channels with
a correct four-phase bundled-data handshake, consumes its result channels the
same way, and compares what came out against a reference computed in Python
from the same inputs.  Disagreement is reported as WHAT DIFFERED and the
process exits nonzero.

USAGE

    python3 bdc/simcheck.py build/frontend/test_loop_free/comp/handshake_transformed.mlir
    python3 bdc/simcheck.py build/frontend/gcd/comp/handshake_transformed.mlir

Run from the repo root (paths above are relative to it).  Everything this
writes goes under cells/build/kernelsim/ -- never cells/build/pnr/, which is
someone else's place-and-route job, and never cells/rtl/, which is frozen.

WHAT "PASS" MEANS AND DOES NOT MEAN

A pass means: every vector's output channel(s) produced exactly one token,
its value matched the Python reference, and the token counts on every output
channel equal the number of vectors sent (so a kernel that quietly drops a
transaction cannot pass by coincidence).  It does NOT mean the routed design
is correct -- this is sim/bd_prims_sim.v arc-only timing, same caveat
run_sim.sh's header already states.

REFERENCE IMPLEMENTATIONS

Keyed by handshake.func name, in REFS below.  A kernel with no entry there
fails loudly rather than being skipped -- see main().

THE --dut OVERRIDE

For proving the gate has teeth: point --dut at a hand-corrupted copy of a
previously generated Verilog file (module bdc_<name>, same port list) instead
of regenerating from the .mlir.  simcheck.py does not silently accept this on
faith -- it is exactly the same file the ordinary run produces, edited by
hand, and the reference is still computed from the true C semantics, so any
edit that changes what the circuit computes gets caught the same way a real
miscompile would.
"""

import argparse
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import emit  # noqa: E402
from hs import parse  # noqa: E402

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CELLS = os.path.join(REPO, "cells")
OUTDIR = os.path.join(CELLS, "build", "kernelsim")


# ---------------------------------------------------------------------------
# 32-bit two's complement helpers.  Hardware wires are unsigned bit patterns;
# C/MLIR semantics are signed.  u() is "what the wire holds", s() is "what a
# signed comparison or arithmetic-shift sees".

def u(x, w=32):
    return x & ((1 << w) - 1) if w else 0


def s(x, w=32):
    x = u(x, w)
    return x - (1 << w) if x >= (1 << (w - 1)) else x


# ---------------------------------------------------------------------------
# Reference implementations, transcribed from the kernels' own C source
# (dynamatic/integration-test/<kernel>/<kernel>.c) -- NOT from the .mlir, and
# NOT from bdc/emit.py.  The whole point is an answer that does not share
# assumptions with the thing being checked.

def ref_test_loop_free(args):
    """dynamatic/integration-test/test_loop_free/test_loop_free.c"""
    a, b, c, d = (s(args[n]) for n in ("a", "b", "c", "d"))
    if a > 0:
        r = b + c + d
    elif b < 0:
        r = a + d
    else:
        r = a
    return {"out0": u(r)}


def ref_gcd(args):
    """dynamatic/integration-test/gcd/gcd.c -- Stein's algorithm."""
    a, b = (s(args[n]) for n in ("a", "b"))

    def ctz_shift(x):
        while x != 0 and (x & 1) == 0:
            x >>= 1
        return x

    if a == 0:
        return {"out0": u(b)}
    if b == 0:
        return {"out0": u(a)}

    k = 0
    while ((a | b) & 1) == 0:
        a >>= 1
        b >>= 1
        k += 1

    a = ctz_shift(a)
    b = ctz_shift(b)

    while a != 0:
        diff = a - b
        if a < b:
            b = a
        a = diff if diff >= 0 else -diff
        a = ctz_shift(a)

    return {"out0": u(b << k)}


# --- kernels/ -- written for this backend, not shipped by Dynamatic --------

def ref_collatz(args):
    """kernels/collatz/collatz.c -- Collatz stopping time."""
    n = s(args["n"])
    steps = 0
    while n != 1:
        n = s(n >> 1) if (n & 1) == 0 else s(3 * n + 1)
        steps = s(steps + 1)
    return {"out0": u(steps)}


def ref_collatz64(args):
    """kernels/collatz64/collatz64.c -- same, on a 64-bit datapath."""
    n = s(args["n"], 64)
    steps = 0
    while n != 1:
        n = s(n >> 1, 64) if (n & 1) == 0 else s(3 * n + 1, 64)
        steps = s(steps + 1)
    return {"out0": u(steps)}


def ref_ipow(args):
    """kernels/ipow/ipow.c -- binary exponentiation."""
    b, e = s(args["b"]), s(args["e"])
    r = 1
    while e > 0:
        if (e & 1) == 1:
            r = s(r * b)
        b = s(b * b)
        e = e >> 1
    return {"out0": u(r)}


def ref_xorshift(args):
    """kernels/xorshift/xorshift.c -- Marsaglia xorshift32."""
    x, rounds = u(args["seed"]), s(args["rounds"])
    i = 0
    while i < rounds:
        x = u(x ^ u(x << 13))
        x = u(x ^ (x >> 17))
        x = u(x ^ u(x << 5))
        i += 1
    return {"out0": u(x)}


def ref_isprime(args):
    """kernels/isprime/isprime.c -- trial division, shift-subtract modulo."""
    n = s(args["n"])
    if n < 2:
        return {"out0": u(0)}
    d = 2
    while s(d * d) <= n:
        r, sh, half = n, d, n >> 1
        while sh <= half:
            sh = s(sh << 1)
        while sh >= d:
            if r >= sh:
                r = s(r - sh)
            sh = sh >> 1
        if r == 0:
            return {"out0": u(0)}
        d = s(d + 1)
    return {"out0": u(1)}


REFS = {"test_loop_free": ref_test_loop_free, "gcd": ref_gcd,
        "collatz": ref_collatz, "collatz64": ref_collatz64,
        "ipow": ref_ipow, "xorshift": ref_xorshift,
        "isprime": ref_isprime}


# ---------------------------------------------------------------------------
# Test vectors, per kernel.  Chosen to hit every branch the C source has, not
# just the one example CALL_KERNEL uses.

VECTORS = {
    "test_loop_free": [
        # a>0 -> b+c+d
        dict(a=1, b=-1, c=2, d=3),
        dict(a=10, b=-20, c=30, d=-5),
        dict(a=0x7FFFFFFF, b=0x7FFFFFFF, c=0x7FFFFFFF, d=1),   # wraps
        # a<=0, b<0 -> a+d
        dict(a=-5, b=-3, c=7, d=11),
        dict(a=-0x80000000, b=-1, c=0, d=0),                   # INT_MIN, no overflow
        dict(a=-1, b=-0x80000000, c=0, d=0x7FFFFFFF),
        # a<=0, b>=0 -> a
        dict(a=-5, b=2, c=1, d=1),
        dict(a=0, b=0, c=100, d=200),                          # a==0, b==0 boundary
    ],
    "gcd": [
        dict(a=0, b=5),
        dict(a=7, b=0),
        dict(a=12, b=18),
        dict(a=48, b=18),
        dict(a=1, b=1),
        dict(a=17, b=5),
    ],
    # --- kernels/ ----------------------------------------------------------
    # collatz: n=1 never enters the loop; 27 is the classic long trajectory
    # (111 steps, peak 9232). Nothing here leaves int32 -- the first n whose
    # trajectory does is 113383, which is collatz64's job.
    "collatz": [
        dict(n=1), dict(n=2), dict(n=3), dict(n=6),
        dict(n=7), dict(n=27), dict(n=97), dict(n=703),
    ],
    # collatz64: 113383 is exactly the smallest n whose trajectory leaves
    # int32, so this vector is one a 32-bit datapath cannot answer at all.
    "collatz64": [
        dict(n=1), dict(n=27), dict(n=113383),
    ],
    # ipow: e=0 skips the loop; (5,14) and (7,11) wrap int32 on the way.
    "ipow": [
        dict(b=3, e=0), dict(b=3, e=1), dict(b=2, e=10),
        dict(b=3, e=7), dict(b=-2, e=3), dict(b=-3, e=4),
        dict(b=7, e=11), dict(b=5, e=14),
    ],
    # xorshift: rounds=0 must pass the seed through untouched.
    "xorshift": [
        dict(seed=2463534242, rounds=0), dict(seed=2463534242, rounds=1),
        dict(seed=2463534242, rounds=2), dict(seed=2463534242, rounds=4),
        dict(seed=1, rounds=3), dict(seed=-1, rounds=2),
    ],
    # isprime: below 2, even, odd composite, prime, square of a prime.
    "isprime": [
        dict(n=-7), dict(n=0), dict(n=1), dict(n=2), dict(n=3),
        dict(n=4), dict(n=9), dict(n=91), dict(n=97), dict(n=113),
    ],
}


# ---------------------------------------------------------------------------
# Verilog generation.  Every data argument gets a sim/bd_env.v bd_source;
# every data result gets a bd_sink.  Control channels (width 0) have no data
# net at all -- bd_source/bd_sink require W>=1 -- so they get the two tiny
# control-only endpoints defined in CTL_HELPERS, which are the same protocol
# minus the data bus.

CTL_HELPERS = """
// Control-only bench endpoints -- bd_source/bd_sink from sim/bd_env.v, minus
// the data bus, for channels bdc/emit.py gives no data net at all (width 0).
// Same SETUP/HOLD constants as bd_env.v, so channel timing is comparable.
module simcheck_ctl_src (output reg req, input wire ack);
    integer nsent;
    initial begin req = 1'b0; nsent = 0; end
    task send;
    begin
        #3000;
        req = 1'b1;
        wait (ack === 1'b1);
        req = 1'b0;
        wait (ack === 1'b0);
        nsent = nsent + 1;
    end
    endtask
endmodule

module simcheck_ctl_snk #(parameter integer HOLD = 2000)
    (input wire req, output reg ack);
    integer n;
    initial begin ack = 1'b0; n = 0; end
    always begin
        wait (req === 1'b1);
        #HOLD;
        n = n + 1;
        ack = 1'b1;
        wait (req === 1'b0);
        #HOLD;
        ack = 1'b0;
    end
endmodule
"""


def _lit(width, value):
    width = max(width, 1)
    nhex = (width + 3) // 4
    return f"{width}'h{u(value, width):0{nhex}x}"


def gen_testbench(func, vectors, expected, tb_name, dut_module):
    """One self-checking testbench, as Verilog text.

    `vectors` is a list of {argname: int} for DATA args (control args need no
    value).  `expected` is the matching list of {resname: int}, already
    reference-computed.
    """
    # A memref argument is not a channel (see bdc/emit.py's Emitter.memrefs)
    # -- it gets no _req/_ack/_data port on the generated module at all, so a
    # source/sink for it here would drive a port that does not exist.
    args = [a for a in func.args if not a.raw.startswith("memref")]
    results = [r for r in func.results]

    lines = [CTL_HELPERS, f"`timescale 1ps / 1ps", "", f"module {tb_name};",
             "", "    localparam integer H = `BD_HOP_PS;",
             "    localparam integer T = 12 * H;", "",
             "    integer errors = 0;", "    integer cur = -1;",
             "    reg rst = 1'b1;", ""]

    def bname(ch):
        return emit.portname(ch.name)

    # -- wires and driver/sink instances ------------------------------------
    conns = ["        .rst(rst),"]
    for a in args:
        b = bname(a)
        lines.append(f"    wire {b}_req, {b}_ack;")
        if not a.is_control:
            w = max(a.width, 1)
            lines.append(f"    wire [{w - 1}:0] {b}_data;")
            lines.append(f"    bd_source #(.W({w})) {b}_src "
                         f"(.req({b}_req), .ack({b}_ack), .data({b}_data));")
            conns.append(f"        .{b}_req({b}_req), .{b}_ack({b}_ack), "
                        f".{b}_data({b}_data),")
        else:
            lines.append(f"    simcheck_ctl_src {b}_src "
                         f"(.req({b}_req), .ack({b}_ack));")
            conns.append(f"        .{b}_req({b}_req), .{b}_ack({b}_ack),")

    for r in results:
        b = bname(r)
        lines.append(f"    wire {b}_req, {b}_ack;")
        if not r.is_control:
            w = max(r.width, 1)
            lines.append(f"    wire [{w - 1}:0] {b}_data;")
            lines.append(f"    bd_sink #(.W({w})) {b}_snk "
                         f"(.req({b}_req), .ack({b}_ack), .data({b}_data));")
            conns.append(f"        .{b}_req({b}_req), .{b}_ack({b}_ack), "
                        f".{b}_data({b}_data),")
        else:
            lines.append(f"    simcheck_ctl_snk {b}_snk "
                         f"(.req({b}_req), .ack({b}_ack));")
            conns.append(f"        .{b}_req({b}_req), .{b}_ack({b}_ack),")
    conns[-1] = conns[-1].rstrip(",") + ");"

    lines.append("")
    lines.append(f"    {dut_module} uut (")
    lines.extend(conns)
    lines.append("")

    # -- one block per vector -------------------------------------------
    lines.append("    initial begin")
    lines.append(f'        $display("{tb_name}");')
    # Hold reset until the power-up X has drained all the way out of the
    # design's longest combinational run, and then some.  This is not
    # conservatism for its own sake: release it early and a C-element latches
    # C(x, .) = x into its own feedback loop, where it stays -- there is no
    # clock edge to wash it out, and the symptom is a wedge with an `x` on an
    # ack, indistinguishable at first glance from a real deadlock.  Asserting
    # reset is monotonic and safe, so the only cost of holding it is sim time,
    # and the hold scales with the design because the settling time does.
    lines.append(f"        #({max(64, 4 * len(func.nodes))} * T);")
    lines.append("        rst = 1'b0;")
    lines.append("        #(8 * T);")
    lines.append("")

    for idx, (vec, exp) in enumerate(zip(vectors, expected)):
        lines.append(f"        // -- vector {idx}: {vec} -> {exp}")
        lines.append(f"        cur = {idx};")
        lines.append("        fork")
        for a in args:
            b = bname(a)
            if a.is_control:
                lines.append(f"            {b}_src.send;")
            else:
                val = vec[a.name]
                lines.append(f"            {b}_src.send({_lit(a.width, val)});")
        for r in results:
            b = bname(r)
            lines.append(f"            wait ({b}_snk.n == {idx + 1});")
        lines.append("        join")
        for r in results:
            b = bname(r)
            if not r.is_control:
                exp_val = exp[r.name]
                lines.append(
                    f'        if ({b}_snk.seen[{idx}] !== {_lit(r.width, exp_val)}) begin')
                lines.append("            errors = errors + 1;")
                lines.append(
                    f'            $display("  FAIL vector {idx} ({vec}): '
                    f'{b} got %0d (0x%h) expected %0d (0x%h)", '
                    f"$signed({b}_snk.seen[{idx}]), {b}_snk.seen[{idx}], "
                    f"$signed({_lit(r.width, exp_val)}), {_lit(r.width, exp_val)});")
                lines.append("        end")
        lines.append("        #(4 * T);")
        lines.append("")

    n = len(vectors)
    lines.append("        // Teeth: a channel that never produced a token would pass every")
    lines.append("        // comparison above by having nothing to compare.  Assert the")
    lines.append("        // count explicitly, on every output channel.")
    for r in results:
        b = bname(r)
        lines.append(f"        if ({b}_snk.n != {n}) begin")
        lines.append("            errors = errors + 1;")
        lines.append(
            f'            $display("  FAIL {b} produced %0d token(s), expected {n}", {b}_snk.n);')
        lines.append("        end")

    lines.append("")
    lines.append(f'        if (errors == 0) $display("{tb_name} PASS");')
    lines.append(f'        else             $display("{tb_name} FAIL (%0d)", errors);')
    lines.append("        $finish;")
    lines.append("    end")
    lines.append("")
    # A bare "timeout" says the design wedged and nothing else, which is the
    # least useful thing a self-reporting bench can say.  Name the vector it
    # was on and print every endpoint's count: a source whose nsent is short
    # by one never got its ack, a sink whose n is short never got its token,
    # and which of those it is decides where to look next.
    lines.append("    initial begin")
    lines.append("        #40_000_000;")
    lines.append(f'        $display("{tb_name} FAIL (timeout) on vector %0d", cur);')
    for a in args:
        b = bname(a)
        lines.append(f'        $display("    src {b}: %0d sent, req=%b ack=%b",'
                     f" {b}_src.nsent, {b}_req, {b}_ack);")
    for r in results:
        b = bname(r)
        lines.append(f'        $display("    snk {b}: %0d seen, req=%b ack=%b",'
                     f" {b}_snk.n, {b}_req, {b}_ack);")
    lines.append("        $finish;")
    lines.append("    end")
    lines.append("")
    lines.append("`ifdef SIMCHECK_VCD")
    lines.append("    initial begin")
    lines.append(f'        $dumpfile("{tb_name}.vcd");')
    lines.append(f"        $dumpvars(0, {tb_name});")
    lines.append("    end")
    lines.append("`endif")
    lines.append("endmodule")
    return "\n".join(lines)


# ---------------------------------------------------------------------------

def run_iverilog(dut_path, tb_path, tb_name, route_ps=0, vcd=False):
    os.makedirs(OUTDIR, exist_ok=True)
    vvp = os.path.join(OUTDIR, f"{tb_name}.vvp")
    log = os.path.join(OUTDIR, f"{tb_name}.log")
    rtl_glob = os.path.join(CELLS, "rtl", "*.v")
    cmd = (f"iverilog -g2012 -gspecify -Wall -Wno-timescale "
          f"-DBD_ROUTE_PS={route_ps} {'-DSIMCHECK_VCD' if vcd else ''} -o {vvp} "
          f"{CELLS}/sim/bd_prims_sim.v {CELLS}/sim/bd_env.v {rtl_glob} "
          f"{dut_path} {tb_path}")
    with open(log, "w") as f:
        cp = subprocess.run(cmd, shell=True, stdout=f, stderr=subprocess.STDOUT)
    if cp.returncode != 0:
        print(f"COMPILE FAIL  {tb_name}  (see {log})")
        with open(log) as f:
            print(f.read())
        return False, log
    cp = subprocess.run(["vvp", vvp], stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT, text=True, cwd=OUTDIR)
    with open(log, "a") as f:
        f.write(cp.stdout)
    print(cp.stdout)
    ok = f"{tb_name} PASS" in cp.stdout
    return ok, log


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mlir")
    ap.add_argument("--dut", help="use this Verilog file instead of regenerating "
                    "(module bdc_<name>, --no-top shape) -- for the corruption "
                    "proof, not ordinary use")
    ap.add_argument("--route-ps", type=int, default=0,
                    help="BD_ROUTE_PS, as in run_sim.sh")
    ap.add_argument("--vectors", type=int, default=0,
                    help="use only the first N vectors (0 = all)")
    ap.add_argument("--vcd", action="store_true",
                    help="dump a VCD next to the log, for when the failure is "
                         "a wedge rather than a wrong answer")
    args = ap.parse_args()

    funcs = [f for f in parse.parse_module(open(args.mlir).read(),
                                          filename=args.mlir)
            if not f.is_declaration]
    if len(funcs) != 1:
        print(f"expected exactly one handshake.func in {args.mlir}, "
             f"found {len(funcs)}", file=sys.stderr)
        return 2
    func = funcs[0]
    name = func.name

    if name not in REFS:
        print(f"simcheck: no reference implementation registered for "
             f"kernel {name!r}. Known: {sorted(REFS)}. Add one to "
             f"bdc/simcheck.py's REFS -- guessing is exactly what this gate "
             f"exists to refuse.", file=sys.stderr)
        return 2
    if name not in VECTORS:
        print(f"simcheck: no test vectors registered for kernel {name!r}.",
             file=sys.stderr)
        return 2

    os.makedirs(OUTDIR, exist_ok=True)

    if args.dut:
        dut_path = args.dut
        print(f"using hand-supplied DUT: {dut_path} (NOT regenerated from the .mlir)")
    else:
        text, _func2, delays = emit.generate(args.mlir, top=False)
        dut_path = os.path.join(OUTDIR, f"{name}_dut.v")
        with open(dut_path, "w") as f:
            f.write(text)
        print(f"regenerated {dut_path}: module bdc_{name}, {len(delays)} matched delay(s)")

    vectors = VECTORS[name]
    if args.vectors:
        vectors = vectors[:args.vectors]
    expected = [REFS[name](v) for v in vectors]

    print(f"{len(vectors)} test vector(s) for {name}:")
    for v, e in zip(vectors, expected):
        print(f"  {v} -> {e}")

    tb_name = f"tb_simcheck_{name}"
    tb_text = gen_testbench(func, vectors, expected, tb_name, f"bdc_{name}")
    tb_path = os.path.join(OUTDIR, f"{tb_name}.v")
    with open(tb_path, "w") as f:
        f.write(tb_text)
    print(f"wrote {tb_path}")

    ok, log = run_iverilog(dut_path, tb_path, tb_name, route_ps=args.route_ps,
                           vcd=args.vcd)
    if ok:
        print(f"PASS  {tb_name}  (log: {log})")
        return 0
    else:
        print(f"FAIL  {tb_name}  (log: {log})")
        return 1


if __name__ == "__main__":
    sys.exit(main())
