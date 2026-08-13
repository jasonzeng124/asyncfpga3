#!/usr/bin/env python3
"""Stage 3: the compute-unit wrapper.

This is the one genuinely new cell class in the backend, and the first time
yosys-optimised logic sits *inside* a bundled-data unit.  Everything in
cells/rtl/ is hand-written and hand-costed; a compute unit is neither, so its
matched delay cannot be known until the design is routed.

The shape is the same for every operation:

    both operands must have arrived           -> bd_join
    data goes through ordinary combinational logic
    ack passes straight back through the join
    req_out = delta(req_in)                   -> bd_delay, sized post-route

Three things here are not free choices, and each one is a constraint the rest
of the toolchain already imposes:

  The instance named `uor`.  verify/tighten.py finds the cells it must audit
  by looking for `<cell>.uor`, and its own comment says why: keying off the
  delay chain instead was tried and was wrong, because bd_delay #(.N(0)) is a
  bare wire, so a cell with NO delay -- the case that most needs auditing --
  left nothing in the netlist to find and was skipped silently.  A generated
  unit without a `uor` would be skipped the same way.  It costs nothing: a
  pass-through LUT1 in front of a LUT1 delay chain is just one more element
  of that chain, so DELAY is one shorter to compensate.

  The `BD_SZ_*` define.  verify/teeth.sh and verify/resize.sh drive a design
  only by overriding `define BD_SZ_*` through BD_SIZES, and never edit
  source.  A generator that inlined delay lengths as literals would turn both
  into silent no-ops while every other gate still passed.  Every delay this
  emits gets a key, with an `ifndef` default, exactly as verify/soak_top.v
  spells it.

  The delay is a PLACEHOLDER and is deliberately generous.  tighten.py
  tightens and never pads; a delay that has to GROW after routing is a
  bundling violation, not a sizing result.  Starting too long is a slow
  design, starting too short is a broken one.
"""

import argparse
import sys

# Operations whose result is the full operand width, and the Verilog
# expression that computes them.  `trunci`, `extui` and `extsi` are absent on
# purpose: they are bus slices and concatenations, i.e. wires, and belong in
# the emitter rather than here.
BINARY = {
    "addi":  "{a} + {b}",
    "subi":  "{a} - {b}",
    "muli":  "{a} * {b}",
    "andi":  "{a} & {b}",
    "ori":   "{a} | {b}",
    "xori":  "{a} ^ {b}",
    "shli":  "{a} << {b}",
    "shrui": "{a} >> {b}",
    "shrsi": "$signed({a}) >>> {b}",
}

# cmpi carries its predicate as a bare keyword argument (`cmpi sgt, %a, %b`),
# which the reader stores as a LiteralArg rather than an attribute.  Signed
# predicates need $signed() or Verilog compares as unsigned and silently
# gets large negative numbers wrong.
CMPI = {
    "eq":  "{a} == {b}",
    "ne":  "{a} != {b}",
    "slt": "$signed({a}) <  $signed({b})",
    "sle": "$signed({a}) <= $signed({b})",
    "sgt": "$signed({a}) >  $signed({b})",
    "sge": "$signed({a}) >= $signed({b})",
    "ult": "{a} <  {b}",
    "ule": "{a} <= {b}",
    "ugt": "{a} >  {b}",
    "uge": "{a} >= {b}",
}

# Starting delay, in LUT1 links, by how deep the logic is.  A placeholder, and
# stated as such: these are not measurements, they are "long enough that
# tighten.py has something to cut".  The one number with a reason behind it is
# muli, where the logic is a real tree rather than a carry chain.
DEFAULT_DELAY = {
    "wide": 4,    # bitwise ops: one LUT, no carry
    "carry": 8,   # add/sub/compare: a carry chain
    "shift": 8,   # barrel shifter
    "mul": 24,    # multiplier tree
}


def _depth_class(op):
    if op == "muli":
        return "mul"
    if op in ("addi", "subi", "cmpi"):
        return "carry"
    if op in ("shli", "shrui", "shrsi"):
        return "shift"
    return "wide"


def unit_name(op, width, pred=None):
    return f"bdc_{op}{'_' + pred if pred else ''}_{width}"


def emit_unit(op, width, pred=None):
    """One compute unit as a self-contained Verilog module."""
    name = unit_name(op, width, pred)
    key = f"BD_SZ_{name.upper()}"
    default = DEFAULT_DELAY[_depth_class(op)]

    if op == "cmpi":
        if pred not in CMPI:
            raise ValueError(f"unknown cmpi predicate {pred!r}")
        expr = CMPI[pred].format(a="a_data", b="b_data")
        out_w, nin = 1, 2
    elif op == "select":
        expr = "s_data[0] ? a_data : b_data"
        out_w, nin = width, 3
    elif op in BINARY:
        expr = BINARY[op].format(a="a_data", b="b_data")
        out_w, nin = width, 2
    else:
        raise ValueError(f"no compute unit for {op!r}")

    # Input channels.  `select` takes its 1-bit condition as a third channel:
    # handshake.select is an ARITH op (HandshakeArithOps.td), so all of its
    # operands are consumed and all must have arrived -- which is a join, not
    # a bd_mux.  Mapping it to bd_mux would leave the unselected input's token
    # in place and leak one token per firing.  See bdc/AUDIT.md section 3.
    chans = ["a", "b"] + (["s"] if op == "select" else [])
    cw = {"a": width, "b": 1 if op == "select" else width, "s": 1}

    ports, decls = [], []
    for c in chans:
        ports += [f"{c}_req", f"{c}_ack", f"{c}_data"]
        decls += [f"     input  wire             {c}_req,",
                  f"     output wire             {c}_ack,",
                  f"     input  wire [{cw[c] - 1}:0]{' ' * max(0, 7 - len(str(cw[c] - 1)))}{c}_data,"]
    if op == "select":
        cw["b"] = width
        decls[4] = f"     input  wire [{width - 1}:0]{' ' * max(0, 7 - len(str(width - 1)))}b_data,"

    req_cat = "{" + ", ".join(f"{c}_req" for c in reversed(chans)) + "}"
    ack_cat = "{" + ", ".join(f"{c}_ack" for c in reversed(chans)) + "}"

    return f"""
// {op}{' ' + pred if pred else ''}, {width}-bit.  Generated by bdc/compute.py -- do not edit.
//
// Matched delay `{key}` is a PLACEHOLDER ({default} links).  verify/tighten.py
// sizes it against measured routed arrival times after place-and-route, and
// it only ever shrinks.  If it has to grow, that is a bundling violation.
`ifndef {key}
 `define {key} {default}
`endif

`default_nettype none
module {name}
    (input  wire             rst,
{chr(10).join(decls)}
     output wire             z_req,
     input  wire             z_ack,
     output wire [{out_w - 1}:0]{' ' * max(0, 7 - len(str(out_w - 1)))}z_data);

    // Every operand must have arrived before the logic means anything.
    wire joined;
    bd_join #(.N({nin})) ujoin (
        .rst(rst), .req_in({req_cat}), .ack_out({ack_cat}),
        .req(joined), .ack(z_ack));

    // The request boundary.  tighten.py locates a cell to audit by finding
    // `<cell>.uor`; without this instance a generated unit is skipped
    // silently, which is the one failure mode that pass was written to
    // avoid.  It is also just the first link of the delay line.
    wire either;
    (* keep *) LUT1 #(.INIT(2'h2)) uor (.I0(joined), .O(either));
    bd_delay #(.N(`{key})) udly (.a(either), .z(z_req));

    // The datapath.  yosys picks the implementation; the matched delay is
    // what makes whatever it picks safe.
    assign z_data = {expr};
endmodule
`default_nettype wire
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("op", help="addi, cmpi, select, ...")
    ap.add_argument("width", type=int)
    ap.add_argument("--pred", help="cmpi predicate (sgt, slt, eq, ...)")
    args = ap.parse_args()
    sys.stdout.write(emit_unit(args.op, args.width, args.pred))


if __name__ == "__main__":
    main()
