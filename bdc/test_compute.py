#!/usr/bin/env python3
"""Correctness gate for bdc/compute.py's datapaths, against Verilog itself.

Every other gate in this project asks whether a design ROUTES and whether its
matched delay is long enough.  None of them asks whether it computes the right
answer, and for the hand-written library that is fine: those cells are control
logic whose behaviour tb_*.v checks directly.

The compute units are different, and the comparison tree is different again.
`a > b` is one token that cannot be wrong; a hand-rolled (greater, equal)
prefix tree is about forty lines of index arithmetic that can be wrong in a way
nothing else here would notice -- fold hi and lo the wrong way round and it
still routes, still meets its bundling constraint, still passes flow.sh and
tighten.py, and quietly answers the wrong question for most inputs.  So the
tree is checked against the operator it replaced.

The oracle is Verilog's own `>`, `<=`, `$signed()` and friends, evaluated by
the same simulator, in the same run, on the same vectors.  That is deliberate:
a Python reimplementation of two's complement would be a second thing to get
wrong, and agreement between two of my own mistakes proves nothing.

Widths are exhaustive where exhaustive is cheap (1..5 bits: every ordered pair)
and randomised above, with the boundaries every comparator gets wrong pinned
down explicitly -- 0, 1, all-ones, the sign bit alone, and the two values
either side of it.

Run:  python3 bdc/test_compute.py
"""

import os
import random
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import compute  # noqa: E402

PREDS = sorted(compute.CMPI)
EXHAUSTIVE_UPTO = 5
WIDTHS = [1, 2, 3, 5, 8, 16, 32]
RANDOM_VECTORS = 400

# The other units are one operator each and so are far less likely to be wrong
# than the tree -- but "less likely" is not a gate, and three of them have a
# real trap in them.  shrsi must be an ARITHMETIC shift, and writing `>>`
# instead of `>>>` is invisible until a negative number arrives.  select must
# consume its condition's low bit, and `s_data ? ...` on a 1-bit wire happens
# to work while `s_data[0]` is what is meant.  Verilog's own operator is the
# oracle for all of them, exactly as for cmpi.
BINARY_REF = {
    "addi": "a + b", "subi": "a - b", "muli": "a * b",
    "andi": "a & b", "ori": "a | b", "xori": "a ^ b",
    "shli": "a << b", "shrui": "a >> b", "shrsi": "$signed(a) >>> b",
}


def vectors(width):
    """Test inputs for one width: exhaustive when small, edges plus random
    otherwise.  The edges are the values a comparator gets wrong -- zero, one,
    all-ones, and the two straddling the sign boundary."""
    m = (1 << width) - 1
    if width <= EXHAUSTIVE_UPTO:
        return [(a, b) for a in range(m + 1) for b in range(m + 1)]
    edge = {0, 1, m, m >> 1, (m >> 1) + 1, 1 << (width - 1)}
    edge = {v & m for v in edge}
    out = [(a, b) for a in edge for b in edge]
    rnd = random.Random(20260813)
    out += [(rnd.getrandbits(width), rnd.getrandbits(width))
            for _ in range(RANDOM_VECTORS)]
    out += [(v, v) for v in edge]          # equality is the easy case to miss
    return out


def build_tb(op, width, pred, vecs):
    """A testbench holding the generated unit's datapath beside the operator it
    replaced.  Only the combinational half is exercised -- the handshake is not
    what is under test here, and driving it would mean writing a protocol model
    whose own bugs would show up as datapath failures."""
    unit = compute.emit_unit(op, width, pred)
    name = compute.unit_name(op, width, pred)
    if op == "cmpi":
        ref = {
            "eq": "a == b", "ne": "a != b",
            "ult": "a <  b", "ule": "a <= b", "ugt": "a >  b", "uge": "a >= b",
            "slt": "$signed(a) <  $signed(b)", "sle": "$signed(a) <= $signed(b)",
            "sgt": "$signed(a) >  $signed(b)", "sge": "$signed(a) >= $signed(b)",
        }[pred]
        out_w, third = 1, ""
    elif op == "select":
        # The condition rides on a third channel and is taken from the vector's
        # low bit of `a`, so it varies over the whole sweep rather than sitting
        # at one value while the datapath is checked.
        ref = "a[0] ? a : b"
        out_w, third = width, "        .s_req(1'b0), .s_ack(s_ack), .s_data(a[0]),\n"
    else:
        ref = BINARY_REF[op]
        out_w, third = width, ""

    # Every data input is driven, never left dangling: an unconnected input is
    # x in Verilog, x propagates through the tree, and !== against a real value
    # would then fail on every vector rather than none -- a failure mode that
    # looks like a broken comparator instead of a broken testbench.
    # `want` is sized to the unit's own output width before comparing.  Verilog
    # widens both sides of == to the wider operand, so an unsized reference
    # would let a truncating unit agree with a non-truncating operator and the
    # gate would pass on a design that drops its top bits.
    label = f"{op}{'.' + pred if pred else ''}"
    body = "\n".join(
        f"        a = {width}'d{a}; b = {width}'d{b}; #1;\n"
        f"        want = {ref};\n"
        f"        if (z_data !== want) begin\n"
        f"            $display(\"MISMATCH w={width} {label} a=%0d b=%0d "
        f"got=%h want=%h\", a, b, z_data, want);\n"
        f"            fails = fails + 1;\n"
        f"        end"
        for a, b in vecs)

    return f"""{unit}
`default_nettype none
module tb;
    reg [{width - 1}:0] a, b;
    reg rst = 1'b0;
    wire a_ack, b_ack, s_ack, z_req;
    wire [{out_w - 1}:0] z_data;
    reg  [{out_w - 1}:0] want;
    integer fails = 0;

    {name} uut (
        .rst(rst),
        .a_req(1'b0), .a_ack(a_ack), .a_data(a),
        .b_req(1'b0), .b_ack(b_ack), .b_data(b),
{third}        .z_req(z_req), .z_ack(1'b0), .z_data(z_data));

    initial begin
{body}
        if (fails == 0) $display("OK {width} {label} {len(vecs)} vectors");
        else begin
            $display("FAIL {width} {label}: %0d of {len(vecs)}", fails);
            $fatal(1);
        end
        $finish;
    end
endmodule
`default_nettype wire
"""


def run(op, width, pred, workdir):
    tag = f"{op}{'_' + pred if pred else ''}_{width}"
    src = os.path.join(workdir, f"tb_{tag}.v")
    exe = os.path.join(workdir, f"tb_{tag}")
    with open(src, "w") as fh:
        fh.write(build_tb(op, width, pred, vectors(width)))

    # bd_delay, bd_join and the LUT1 primitive come from the frozen library and
    # its simulation model.  They are instantiated but not exercised: this gate
    # is about z_data, and pulling them in is only so the unit elaborates.
    # Same file list cells/run_sim.sh compiles, and named the same way it names
    # it: -y would not find these, because the library puts several modules per
    # file (bd_join lives in bd_ctl.v) and -y only ever looks for <module>.v.
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    cells = os.path.join(root, "cells")
    srcs = [os.path.join(cells, "sim", "bd_prims_sim.v"),
            os.path.join(cells, "sim", "bd_env.v")]
    srcs += [os.path.join(cells, "rtl", f)
             for f in sorted(os.listdir(os.path.join(cells, "rtl")))
             if f.endswith(".v")]
    cmd = ["iverilog", "-g2012", "-gspecify", "-DBD_ROUTE_PS=0",
           "-o", exe] + srcs + [src]
    c = subprocess.run(cmd, capture_output=True, text=True)
    if c.returncode or not os.path.exists(exe):
        return False, f"compile failed:\n{c.stderr.strip()[:1500]}"
    r = subprocess.run([exe], capture_output=True, text=True)
    return r.returncode == 0, (r.stdout + r.stderr).strip()


def main():
    if not shutil.which("iverilog"):
        print("iverilog not on PATH -- this gate needs a simulator, and "
              "skipping it silently is how a wrong comparator ships")
        return 2

    cases = [("cmpi", p) for p in PREDS]
    cases += [(op, None) for op in sorted(BINARY_REF)]
    cases += [("select", None)]

    workdir = tempfile.mkdtemp(prefix="bdc_compute_")
    passed, failed = 0, []
    for width in WIDTHS:
        for op, pred in cases:
            ok, out = run(op, width, pred, workdir)
            if ok:
                passed += 1
            else:
                failed.append((width, op, pred, out))
                print(f"  FAIL  w={width:<3} {op} {pred or ''}")
    print(f"\n{passed}/{passed + len(failed)} (width, operation) "
          f"combinations match Verilog's own operators")
    if failed:
        for width, op, pred, out in failed:
            print(f"\n=== w={width} {op} {pred or ''} ===\n{out[:2000]}")
        return 1
    shutil.rmtree(workdir, ignore_errors=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
