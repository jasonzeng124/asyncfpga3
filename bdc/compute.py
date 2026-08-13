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
// keep_hierarchy is load-bearing, not tidiness.  flow.sh synthesises with
// -flatten, and without this yosys dissolves the wrapper: the inferred carry
// chain comes out named `$auto$alumacc.cc:...$N.genblk1.slice[0]...carry4`,
// outside this cell's instance prefix entirely.  verify/tighten.py confines
// rule A to `<cell>.*` -- on purpose, so a matched delay is measured against
// its own logic and not against an arrival accumulated across half the design
// -- so a dissolved boundary puts the datapath out of reach and the delay is
// reported as having nothing to wait for.  The cell must survive flattening
// for its own delay to be auditable.
(* keep_hierarchy *)
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


def emit_proto_top(op, width, pred=None):
    """A two-pin top that exercises one unit, in the shape of verify/soak_top.v.

    Two mistakes are baked into this, and both were made before being written
    down.

    The operands must come from real STATE.  The first version derived both
    from pin_in, which looks non-constant but is not: every bit of both
    operands was a function of the same single bit, so the whole sum collapsed
    and yosys folded the adder away -- 14 LUTs, no carry chain, a gate passing
    while measuring nothing.  bd_pipe's latches are keep'd LUT feedback loops
    and so are opaque to folding, which is what makes them usable as a source.

    The environment must not close a COMBINATIONAL LOOP around the unit.  The
    second version fed z_req straight back to z_ack and derived a_req from
    a_ack.  Both are cycles through the cell, and tighten.py's model treats a
    pin on a cycle as a state node -- so every link of the matched delay became
    one, the chain's own tail landed in the cell's start set, and rule A
    measured the request arriving at itself in 0 ps.  The handshake is driven
    from the spine's latched state instead, and the acks are OBSERVED (folded
    into pin_out) rather than fed back.

    This top is not a functioning adder and does not try to be.  Like
    soak_top.v it exists so that nothing folds, nothing merges, and every net
    is real enough for the router -- the gates measure topology and arrival
    times, not arithmetic.
    """
    name = unit_name(op, width, pred)
    out_w = 1 if op == "cmpi" else width
    chans = ["a", "b"] + (["s"] if op == "select" else [])
    # Each channel's request gets a DIFFERENT live signal.  Tying them together
    # would let yosys collapse the join's C-element into a wire.
    drive = {"a": "p_req_out", "b": "spine", "s": "p_data_out[0]"}

    # The spine is sized so every operand gets its OWN slice.  A fixed 16-bit
    # spine looked fine until width 16, where a and b would land on the same
    # bits -- and a + a is a shift, which folds the carry chain away again.
    # Each operand must be a distinct word or the unit under test is not the
    # unit that gets routed.
    nb = max(16, width * 2 + (1 if op == "select" else 0))
    slices = {c: f"p_data_out[{(i + 1) * width - 1}:{i * width}]"
              for i, c in enumerate(["a", "b"])}
    slices["s"] = f"p_data_out[{nb - 1}]"

    seed = int(("5A3C" * (nb // 16 + 1)), 16) & ((1 << (nb - 1)) - 1)

    conns = "\n".join(
        f"        .{c}_req({c}_req), .{c}_ack({c}_ack), "
        f".{c}_data({slices[c]}),"
        for c in chans)

    return f"""
`default_nettype none
module {name}_top (input wire pin_in, output wire pin_out);

    wire rst = pin_in;

    // A free-running spine: the pipe acknowledges itself, so nothing settles
    // and its {nb} latch bits keep changing.
    wire        p_ack_in, p_req_out;
    wire [{nb - 1}:0] p_data_out;
    wire        spine;
    bd_delay #(.N(3)) uspin (.a(p_ack_in), .z(spine));

    bd_pipe #(.W({nb}), .N(4)) upipe (
        .rst(rst),
        .req_in(~spine), .ack_in(p_ack_in),
        .data_in({{{nb - 1}'h{seed:x}, pin_in}}),
        .req_out(p_req_out), .ack_out(p_req_out), .data_out(p_data_out));

    wire {', '.join(f'{c}_req, {c}_ack' for c in chans)}, z_req, z_ack;
    wire [{out_w - 1}:0] z_data;

    // Driven from latched state, never from the unit's own outputs.
{chr(10).join(f'    assign {c}_req = {drive[c]};' for c in chans)}

    {name} uut (
        .rst(rst),
{conns}
        .z_req(z_req), .z_ack(z_ack), .z_data(z_data));

    // The consumer is a latch bit, not z_req: feeding the request back would
    // make the matched delay a cycle and take it out of the analysis.
    assign z_ack = p_data_out[3];

    // EVERY output of the unit is observed here, z_req included.  An output
    // nobody reads is an output yosys deletes: with z_req feeding only z_ack
    // the whole matched delay vanished, and rule A then measured a cell with
    // no delay in it and called that a violation.  The request has to be read
    // somewhere that is not a way back into the cell.
    assign pin_out = ^z_data ^ p_req_out ^ z_req ^ {' ^ '.join(f'{c}_ack' for c in chans)};
endmodule
`default_nettype wire
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("op", help="addi, cmpi, select, ...")
    ap.add_argument("width", type=int)
    ap.add_argument("--pred", help="cmpi predicate (sgt, slt, eq, ...)")
    ap.add_argument("--proto", action="store_true",
                    help="also emit a two-pin prototype top for cells/flow.sh")
    args = ap.parse_args()
    sys.stdout.write(emit_unit(args.op, args.width, args.pred))
    if args.proto:
        sys.stdout.write(emit_proto_top(args.op, args.width, args.pred))


if __name__ == "__main__":
    main()
