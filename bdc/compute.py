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
import os
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

# Placeholder length, in bd_delay links, for a BARE LIBRARY CELL -- a bd_mux
# or the generated arbitrated merge, whose data path is a single datamux LUT
# and so does not grow with width.
#
# This was 4, on the grounds that bd_mux certified at 4 with room to come down
# to 3.  It did -- on ONE route.  Rebuilding gcd with longer compute delays
# moved the placement, and the same uut.umux0 went from peak 664 ps and margin
# +2022 to peak 1984 ps and margin -335.  Nothing about the mux changed; the
# routing around it did.
#
# So a placeholder cannot be sized from one route's measurement, only bounded
# by the worst routing spread seen across routes.  Observed mux peaks top out
# at 2179 ps, which wants 6 links; 12 is two-fold headroom and still small.
# This is the same argument as FLOOR below, and it is the general rule: what a
# small cell races is not its own logic, it is its own wiring.
CELL_DELAY = {"wide": 12}

# The shortest placeholder any compute unit gets, whatever its width.  It is
# not a logic-depth number: it covers the routing spread of a cell's own
# datapath, which is what a narrow op actually races.  Measured -- see
# default_delay() -- from a 1-bit compare that peaked at 3619 ps and wanted 10
# links while several 32-bit adders wanted 4.
FLOOR = 16


def merge_delay(n):
    """Placeholder for an n-input arbitrated merge.

    An n-input merge is a cascade of n-1 bd_arbiters, so its grant is n-1
    arbiter delays deep rather than one.  The flat 4 that served the two-input
    case put the first three-input control_merge 38 ps short.
    """
    return CELL_DELAY["wide"] * (n - 1)


def default_delay(op, width):
    """Placeholder length, in bd_delay links, for one COMPUTE UNIT.

    Width-aware, because the class where it matters is the one whose logic
    depth IS the width.  The flat table above was written before anything had
    been routed, and it was wrong in the one direction that is not allowed:
    verify/tighten.py only ever shrinks a delay, so a length that has to GROW
    after routing is a bundling violation rather than a sizing result.  A
    placeholder that starts too long is merely a slow design and gets
    shortened on the first measurement; one that starts too short is a broken
    design that reports itself broken.

    Calibrated against routed SDF, not guessed.  A link is ~290 ps on these
    routes, and across 66 matched delays in gcd plus 9 in test_loop_free:

      * 32-bit carry chains peak at 3552-5875 ps, wanting 4-10 links
      * 32-bit shifts peak at 7481-8816 ps, wanting 12-25 links -- the barrel
        shifter is by a wide margin the deepest datapath in the op set, and
        the first version of this function extrapolated it from the carry
        chain and came up one link short on ushrsi2
      * bitwise ops and `select` peak at 1399-3229 ps, wanting 0-5 links
      * NARROW ops are not cheap.  A 1-bit compare peaked at 3619 ps and
        wanted 10 links -- more than several 32-bit ones.  Its logic is one
        LUT; what it is racing is the ROUTING of its own datapath, which does
        not shrink with width.  That is why there is a floor at all, and why
        the floor is not small.

    So: a floor that covers routing spread, and a width term only where logic
    depth actually tracks width.  Being generous costs almost nothing -- the
    placeholder is never what ships, verify/resize.sh proposes the measured
    length from the routed SDF and that is what gets built -- while being one
    link short costs a re-route.

      * 32-bit MULTIPLIERS.  The 11152 ps / 16475 ps figures this paragraph
        used to quote were EXTRAPOLATED, for as long as no kernel contained a
        variable x variable multiply -- every multiply the shipped tests have
        is by a literal, and --arith-reduce-strength rewrites those into
        shifts and adds before the backend sees them.  kernels/ipow is the
        first thing that routed one, and BD_DSP=1 is now the default (the
        toolchain bug that made the DSP path compute wrong products is fixed,
        see cells/flow.sh and patches/nextpnr-xilinx-dsp-constpins.patch), so
        this class is now measured rather than guessed on both paths.

        THE DSP PATH IS STILL THE SLOWER OF THE TWO, and by more than the old
        extrapolation assumed.  ipow_ps, nextpnr d216cb36a370f78a, both
        umuli0 and umuli1, 10 placer seeds (default + 1-9), routed (not
        extrapolated) each time:

            DSP48E1 cascade (3 DSPs per 32x32 multiply, 6 total in ipow_ps,
              confirmed in the FASM) peak arrival: 14295-16785 ps
            LUT-array peak arrival, same seeds, same route otherwise: 10806-
              12981 ps

        A 32x32 product needs THREE cascaded DSP48E1s on this part, not two --
        yosys's own stat confirms 3 per multiply -- so the A->P/PCIN->P arc is
        paid three times, and the cascade ends up slower than the LUT array it
        replaced.  DSP48E1 is still worth having: it takes ipow from 3627 to
        1449 occupied LUT sites, 60% off.  It is not worth a shorter matched
        delay, because it does not need one -- it needs a slightly LONGER one
        than the LUT path, and 2*width already covers both.

        WHETHER 2*width CAN BE CUT DOWN FOR THE DSP CASE WAS TESTED, NOT
        GUESSED, by rebuilding and RE-ROUTING ipow_ps at explicit shorter
        DELAY values (BD_MUL_SCALE below) rather than extrapolating from the
        64-link route's own tighten.py recommendation -- shrinking the chain
        moves the placement, so only an actual re-route answers the question:

            48 links (0.75x): a REAL violation, unguarded, on 1 of 5 seeds
              routed -- bridge_i.udut.umuli0, seed 1, margin -1326 ps,
              "PAD to 52 -- VIOLATION".  Rule A's own review margin
              (max(0.2*t_data, 200 ps)) is not a hypothetical here.

            56 links (0.875x): clears rule A's own guard on every one of 5
              seeds sampled (worst raw margin +2749 ps).  But that margin is
              carried entirely by the bd_delay chain's SDF-PREDICTED speed,
              and the chain is the one thing rule A's flat 0.2*peak guard
              was never built to protect -- that is exactly what GUARD_LO
              (verify/skew.py, a 95/95 one-sided bound from five silicon ring
              oscillators built of this same bd_delay primitive) exists for.
              Derating the chain portion of the request by GUARD_LO = 0.772
              -- i.e. asking "does this still hold if the chain runs as fast
              as real silicon has been measured to run" -- turns 3 of the 8
              sampled route/instance margins negative, worst -2178 ps.

        And the number this was supposed to shrink FROM is not comfortably
        clear of that same standard either: at the current 64 links, every
        raw rule A margin across the 10-seed/2-instance sweep is healthy
        (minimum +4906 ps), but the GUARD_LO-derated margin goes negative on
        one of the 20 samples (bridge_i.udut.umuli0, seed 1: -527 ps).

        That -527 ps was then chased out to 25 seeds / 50 samples, because a
        minimum is not a distribution.  It does NOT indicate an under-priced
        delay.  Three columns, same routes:

              raw rule A margin        min  +4906   med +10544   neg  0/50
              derated, + rule A guard  min   -527   med  +4226   neg  1/50
              derated, ordering only   min  +2830   med  +7277   neg  0/50

        The third is the correctness question -- with the chain running at the
        95/95 low corner, does the request still arrive AFTER the data?  It
        does, by at least 2830 ps on the worst of 50 samples.  The one
        negative in the middle row is rule A's own guard (max(0.2*peak,200),
        ~3357 ps at that route's 16785 ps peak) being eaten into, not the
        delay going short.  Stacking rule A's guard on top of a full GUARD_LO
        derate double-counts two independent conservatisms; one tail sample
        landing 527 ps inside the combined pair is not a defect.

        So 64 links is not raised either.  There is no headroom here to
        spend, and -- once the two guards are not stacked -- none needing to
        be added.

        So: NOT re-priced down for BD_DSP.  2*width stays the number for
        `mul` on both paths -- the DSP case does not get a shorter constant
        because the measurement says it cannot safely have one, and the LUT
        case was never the one asking for a change.  A negative result, kept
        rather than an optimistic constant that would have shipped a design
        that only fails at temperature.
    """
    cls = _depth_class(op)
    if cls == "mul":
        # BD_MUL_SCALE is a DIAGNOSTIC knob and nothing else.  When a routed
        # design gives wrong ANSWERS, the first question is whether the
        # matched delay is short -- and the only way to answer it without
        # trusting the same SDF that produced the delay is to make the delay
        # absurdly long and see if the wrongness survives.  If it does, the
        # fault is not timing.  Never set this to ship: a scaled delay is
        # latency on every transaction, which is exactly the cost this
        # backend exists to avoid paying.
        scale = float(os.environ.get("BD_MUL_SCALE", "1"))
        return max(FLOOR, int(2 * width * scale))   # MEASURED on kernels/ipow
    if cls == "shift":
        return max(FLOOR, width)
    if cls == "carry":
        n = max(FLOOR, (3 * width) // 4)
        # A COMPARATOR CARRIES ONE MORE GATE THAN THE OTHER CARRY OPS.  Its
        # result leaves through a kept LUT1 rather than off the carry chain
        # (see the carry-out note in emit_unit), and that LUT is datapath: the
        # matched delay has to cover it.  Adding the LUT without adding this
        # was a real bundling violation, not a theoretical one -- rule A went
        # from clean to `ucmpi1 margin -92, ucmpi10 margin -811` on the very
        # next route, and four gcd vectors that had been passing stopped
        # completing.
        #
        # +6 rather than +3.  The measured shortfall was 1 and 3 links, but a
        # margin is a property of a ROUTE and not of a cell: the same ucmpi
        # cells were +2.0 to +11.1 ns clear on the previous route, which is
        # exactly why quoting that margin as headroom for this change was
        # wrong.  Double the worst observed shortfall, for the same reason
        # CELL_DELAY above is 12 and not 6.
        if op == "cmpi":
            n += 6
        return n
    return FLOOR


def cmp_pair(pred):
    """The (greater, equal) pair a predicate needs, as Verilog text.

    Returns (body_lines, greater_net, equal_net); a net is None when the
    predicate does not mention it, so `eq` builds no comparator chain at all.
    Neither net needs to know whether it serves a signed or an unsigned
    predicate: emit_unit hands over xa/xb, already sign-flipped where that
    applies.

    This was a hand-rolled forty-line (greater, equal) prefix tree, and why it
    stopped being one is the part worth keeping.  `xa > xb` lets yosys infer a
    CARRY4 chain, and on this part that chain DID NOT ROUTE -- "Failed to route
    arc 0 of net uut.$gt$....G[n], from SLICE_X38Y39/D6LUT_O6 to
    SLICE_X40Y39/B1", at width 8 and at 32, on every placer seed tried.  Three
    experiments pinned it to carry chains whose only consumer is the carry OUT:
    cmpi eq routed (equality infers no chain), subi routed (a chain, but its
    sum is used), cmpi sgt did not.  The tree existed because it is the one
    shape of comparison that cannot become a carry chain -- yosys's alumacc
    pass fires on $gt/$lt cells and there were none left to fire on.

    That was a defect in nextpnr-xilinx, not a property of the fabric, and it
    is fixed upstream by c2c05095, "relocate carry-O fabric fanout in ALU
    chains": where a chain bit has fabric fanout on BOTH its sum and its carry
    out, the CARRY4 is split there and the sum duplicated into an ordinary LUT,
    so the two no longer contend for the sub-slice's single output path.
    Confirmed here on 2026-08-14 at both widths, with a real CARRY4 in the
    FASM.  The tree cost about twice the LUTs -- 32-bit prototype top, same
    toolchain: 200 occupied sites for the tree against 177 for the operator --
    and bought nothing once the packer was right.

    So the rule it leaves behind is the opposite of the one it was written
    under: a routing failure in a construct as ordinary as `<` is a toolchain
    bug until proven otherwise, and the first move is to find out what upstream
    has already fixed -- not to write a replacement for the operator.
    """
    tmpl = CMPI[pred]
    lines, g, e = [], None, None
    if "{g}" in tmpl:
        g = "cmp_g"
        lines.append(f"    wire {g} = xa > xb;")
    if "{e}" in tmpl:
        e = "cmp_e"
        lines.append(f"    wire {e} = xa == xb;")
    return lines, g, e


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
    default = default_delay(op, width)

    extra = []
    if op == "cmpi":
        if pred not in CMPI:
            raise ValueError(f"unknown cmpi predicate {pred!r}")
        # Signed compare is unsigned compare on operands with the sign bit
        # flipped: the flip is order-preserving from two's complement onto
        # unsigned, so one comparison serves all ten predicates and there is no
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
        body, g, e = cmp_pair(pred)
        extra.extend(body)
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

    # A COMPARATOR'S RESULT DOES NOT LEAVE THE CELL ON A CARRY-OUT PIN.
    #
    # `xa > xb` is a carry chain, and its answer is the chain's final carry.
    # Written as `assign z_data = cmp_g;` that makes the module's output net
    # driven DIRECTLY by a CARRY4 CO pin -- and a carry-out reaching general
    # routing is the one place this design asks the packer for something it
    # does not ask for anywhere else.
    #
    # It came back wrong.  On the gcd route, ucmpi11 -- `cmpi sgt(diff, -1)`,
    # the sign test that turns `a - b` into `|a - b|` -- returns 0 for every
    # positive input.  The consequences are total and silent: `a = |diff|`
    # becomes `a = -diff`, a goes negative, the outer `while (a != 0)` never
    # terminates, and the kernel spins forever without ever delivering a wrong
    # answer.  Seven of sixteen vectors fail that way on the board and seven in
    # cells/gls; the nine that pass are the ones whose diff is never positive,
    # plus diff == 0, where negating happens to be a no-op.
    #
    # It is not the RTL and it is not synthesis.  `$signed`-free flip-and-
    # compare simulates correctly as source, and the POST-YOSYS netlist for
    # this same unit simulates correctly against the toolchain's own
    # cells_sim.v -- 10 of 10 vectors, including the ones that fail on the
    # board.  Only the ROUTED netlist is wrong, so the fault is introduced
    # between synthesis and the bitstream.
    #
    # The correlation is exact and the sample is the whole design: of every net
    # in the routed gcd, EXACTLY ONE is both a CARRY4 carry-out and a channel
    # data bit, and it is this comparator's output.  `cmpi slt` in the same
    # kernel is correct, and the only structural difference is that its result
    # comes out of a LUT because `~(g | e)` needs one.
    #
    # So give every comparator the LUT that the working predicates got for
    # free.  One LUT per cmpi, `keep` so yosys cannot fold it back out, and one
    # more LUT of depth under a matched delay that rule A already reports +2.0
    # to +11.1 ns of margin on.  This is a WORKAROUND at the point of use, not
    # a diagnosis of the packer: the underlying bug is still in the toolchain
    # and still worth a minimal reproducer -- see [[nextpnr-is-patchable]].
    if op == "cmpi":
        tail = (f"    wire cmp_z = {expr};\n"
                f"    (* keep *) LUT1 #(.INIT(2'h2)) uz (.I0(cmp_z), .O(z_data));")
    else:
        tail = f"    assign z_data = {expr};"

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
{tail}
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
    default = default_delay(op, width)
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
