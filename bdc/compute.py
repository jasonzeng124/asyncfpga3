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

  The `BD_SZ_*` key, and WHERE it lives.  verify/teeth.sh and verify/resize.sh
  drive a design only by overriding `define BD_SZ_*` through BD_SIZES, and
  never edit source.  A generator that inlined delay lengths as literals would
  turn both into silent no-ops while every other gate still passed.

  The first version of this file got the key right and its LOCATION wrong: it
  put `ifndef BD_SZ_BDC_ADDI_8` inside the unit, named after the MODULE.
  verify/tighten.py names a delay after the INSTANCE PATH it found it at --
  `macro('uut')` is `BD_SZ_UUT` -- so resize.sh would have proposed a length
  under a key no source file read, and the whole loop would have been a no-op
  while reporting success.  That is exactly the failure this paragraph exists
  to prevent, reached by a different route.

  It is wrong on the merits too, not merely by convention: a matched delay is a
  property of a ROUTE, so two instances of the same unit in different corners
  of the die need different lengths, and a module-level key cannot express
  that.  So the unit takes `parameter DELAY`, and the instantiating top spells
  the `ifndef` / `define` / `endif` for its own instance path, exactly as
  verify/soak_top.v does for `BD_SZ_UMUX`.

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
# which the reader stores as a LiteralArg rather than an attribute.
#
# Each predicate is (greater, equal) -> expression, over the two outputs of the
# comparison tree below.  Signed predicates are the unsigned ones with the sign
# bit of both operands flipped, which is why there is no $signed() anywhere:
# flipping the MSB maps two's complement onto unsigned in an order-preserving
# way, so one tree serves both.
CMPI = {
    "eq":  "{e}",
    "ne":  "~{e}",
    "ult": "~({g} | {e})",
    "ule": "~{g}",
    "ugt": "{g}",
    "uge": "{g} | {e}",
}
CMPI.update({"s" + k[1:]: v for k, v in CMPI.items() if k.startswith("u")})
SIGNED_CMPI = {"slt", "sle", "sgt", "sge"}

# Starting delay, in LUT1 links, by how deep the logic is.  A placeholder, and
# stated as such: these are not measurements, they are "long enough that
# tighten.py has something to cut".  The one number with a reason behind it is
# muli, where the logic is a real tree rather than a carry chain.
DEFAULT_DELAY = {
    "wide": 4,    # bitwise ops: one LUT, no carry
    "carry": 8,   # add/sub: a carry chain.  compare shares the number but not
                  # the reason -- its (g,e) tree is six levels at 32 bits
    "shift": 8,   # barrel shifter
    "mul": 24,    # multiplier tree
}


def cmp_tree(width):
    """A (greater, equal) prefix tree over a_data and b_data, as Verilog text.

    Returns (body_lines, greater_net, equal_net).

    Writing `a_data > b_data` and letting yosys infer a CARRY4 chain is the
    obvious thing, it produces a smaller netlist, and IT DOES NOT ROUTE ON THIS
    PART.  The failure is worth recording in full, because it took three
    experiments to separate from the two innocent explanations:

      cmpi eq at width 8 routes (no carry chain is inferred for equality).
      subi  at width 8 routes (a carry chain IS inferred, and its sum is used).
      cmpi sgt fails at width 8 and 32, on every placer seed tried, always the
      same way: "Failed to route arc 0 of net uut.$gt$....G[n], from
      SLICE_X38Y39/D6LUT_O6 to SLICE_X40Y39/B1".

    So it is not scale, not the op, and not placement luck -- it is carry
    chains whose only consumer is the carry OUT.  A CARRY4's S and DI inputs
    have no general routing to them; they must come from the LUTs in the same
    slice, and the packer normally guarantees that by co-packing them.  In an
    adder those LUTs also produce the sum, so both halves of the site are
    spoken for.  In a comparator the result is one bit off the top of the
    chain, the S-driving LUTs have a free O5 half, and the fractured-LUT packer
    this library depends on pairs them with unrelated functions -- which strands
    them in a slice the chain is not in, and the arc becomes unroutable.

    That is a property of the packer, not of the design, and it is not one this
    project controls.  So the comparison is built out of ordinary logic that
    cannot be turned into a carry chain at all: yosys's alumacc pass fires on
    $gt/$lt cells, and there are none here to fire on.

    The cost is not obviously worse.  A balanced tree of (g, e) pairs is
    2*(W-1) LUTs and ceil(log2(W)) + 1 deep -- six levels at 32 bits, against
    eight CARRY4s in series.  On this fabric routing dominates so heavily that
    the shallower tree is very likely the faster of the two; tighten.py will
    say, and its answer is the only one that counts.
    """
    # The tree never needs to know whether it is serving a signed or an
    # unsigned predicate: emit_unit hands it xa/xb, already sign-flipped where
    # that applies.
    lines = [f"    wire [{width - 1}:0] g0 = xa & ~xb;",
             f"    wire [{width - 1}:0] e0 = xa ~^ xb;"]
    pairs = [(f"g0[{i}]", f"e0[{i}]") for i in range(width)]

    level = 0
    while len(pairs) > 1:
        level += 1
        nxt, asg = [], []
        # pairs[] stays ordered by significance, index 0 least, so the leftover
        # of an odd level is the most significant group and is appended last,
        # which keeps that order true at the next level.  The recurrence is
        # greater = g_hi | (e_hi & g_lo): get hi and lo the wrong way round and
        # the comparison is silently wrong for exactly the inputs where the
        # high bits decide it, which is most of them.
        for i in range(0, len(pairs) - 1, 2):
            (g_hi, e_hi), (g_lo, e_lo) = pairs[i + 1], pairs[i]
            gn, en = f"g{level}_{i // 2}", f"e{level}_{i // 2}"
            asg.append(f"    wire {gn} = {g_hi} | ({e_hi} & {g_lo});")
            asg.append(f"    wire {en} = {e_hi} & {e_lo};")
            nxt.append((gn, en))
        if len(pairs) % 2:
            nxt.append(pairs[-1])       # odd one out, unchanged, next level
        lines.extend(asg)
        pairs = nxt

    return lines, pairs[0][0], pairs[0][1]


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
    default = DEFAULT_DELAY[_depth_class(op)]

    extra = []
    if op == "cmpi":
        if pred not in CMPI:
            raise ValueError(f"unknown cmpi predicate {pred!r}")
        # Signed compare is unsigned compare on operands with the sign bit
        # flipped: the flip is order-preserving from two's complement onto
        # unsigned, so one tree serves all ten predicates and there is no
        # second code path to get wrong.
        # The sign-bit mask.  At width 1 the sign bit is the ONLY bit, so the
        # zero-padding below it is a zero-width constant, which is not legal
        # Verilog -- write the mask directly instead of concatenating nothing
        # onto it.  A 1-bit signed value is 0 or -1, and this is what makes
        # those compare in the right order.
        flip = None
        if pred in SIGNED_CMPI:
            flip = "1'b1" if width == 1 else f"{{1'b1, {width - 1}'b0}}"
        extra.append(f"    wire [{width - 1}:0] xa = a_data"
                     + (f" ^ {flip};" if flip else ";"))
        extra.append(f"    wire [{width - 1}:0] xb = b_data"
                     + (f" ^ {flip};" if flip else ";"))
        tree, g, e = cmp_tree(width)
        extra.extend(tree)
        expr = CMPI[pred].format(g=g, e=e)
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
    # Only the condition is narrow.  This started as a width table plus a
    # patch-up that rewrote one declaration afterwards, and the patch-up
    # indexed the wrong slot: three declarations per channel means b_data is
    # index 5, not 4, so it overwrote b_ack -- the unit declared b_data twice,
    # had no b_ack at all, and did not elaborate.  Every routing gate was blind
    # to it, because none of them ever built a select.  bdc/test_compute.py is
    # what found it, on the first run that included the op.
    chans = ["a", "b"] + (["s"] if op == "select" else [])
    cw = {"a": width, "b": width, "s": 1}

    decls = []
    for c in chans:
        pad = ' ' * max(0, 7 - len(str(cw[c] - 1)))
        decls += [f"     input  wire             {c}_req,",
                  f"     output wire             {c}_ack,",
                  f"     input  wire [{cw[c] - 1}:0]{pad}{c}_data,"]

    req_cat = "{" + ", ".join(f"{c}_req" for c in reversed(chans)) + "}"
    ack_cat = "{" + ", ".join(f"{c}_ack" for c in reversed(chans)) + "}"

    return f"""
// {op}{' ' + pred if pred else ''}, {width}-bit.  Generated by bdc/compute.py -- do not edit.
//
// DELAY is a PLACEHOLDER ({default} links) and belongs to whoever instantiates
// this, not to the module: verify/tighten.py sizes a delay against measured
// routed arrival times and names its answer after the INSTANCE PATH, so the
// `BD_SZ_*` key has to be spelled at the instance.  It only ever shrinks; a
// delay that has to grow is a bundling violation, not a sizing result.
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
module {name} #(parameter DELAY = {default})
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
    bd_delay #(.N(DELAY)) udly (.a(either), .z(z_req));

    // The datapath.  yosys picks the implementation; the matched delay is
    // what makes whatever it picks safe.
{chr(10).join(extra)}
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
    default = DEFAULT_DELAY[_depth_class(op)]
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
// Matched-delay length.  A PLACEHOLDER, exactly as verify/soak_top.v's are.
//
// The `include is half the mechanism and is easy to leave out, because leaving
// it out fails SILENTLY: flow.sh accepts BD_SIZES, prints "using measured delay
// lengths from ...", copies the file into the build directory, passes
// -DBD_SIZES -- and nothing includes it, so the placeholders are what get
// routed and every gate passes on a design that ignored its own measurements.
// It was left out here once and cost a full route to notice.
//
// The key is named after the INSTANCE, `uut`, because that is what
// verify/tighten.py calls it: macro('uut') -> BD_SZ_UUT.  A key named after
// the module would be proposed by resize.sh, written to sizes.vh, read by
// nothing, and the tightening loop would report success having changed nothing.
`ifdef BD_SIZES
 `include "sizes.vh"
`endif
`ifndef BD_SZ_UUT
 `define BD_SZ_UUT {default}
`endif

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

    {name} #(.DELAY(`BD_SZ_UUT)) uut (
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
