#!/usr/bin/env python3
"""Stage 1 Phase 3: a parsed handshake graph -> bundled-data Verilog.

Every channel becomes three nets and nothing else:

    <v>_req    producer -> consumer
    <v>_ack    consumer -> producer
    <v>_data   producer -> consumer, absent entirely on a control channel

That is the whole data model, and it is only this simple because
--handshake-materialize has already guaranteed one producer and one consumer
per value.  Without that guarantee a channel would be a fan-out problem and
every op lowering would have to solve it again; with it, a channel is a bundle
of wires with exactly two ends.  bdc/AUDIT.md section 5 is where that
guarantee is checked rather than assumed.

WHAT THIS FILE REFUSES TO DO

Guess.  An op with no lowering here raises by name.  A width that cannot be
derived raises by name.  An arity the lowering does not cover raises by name.
The reason is the same one bdc/map.py's header gives: a wrong cell is a silent
miscompile, and every gate in this project measures topology and timing, not
arithmetic -- flow.sh will happily route the wrong circuit, and tighten.py will
happily prove its matched delays are long enough.  Nothing downstream would
catch it.  So the failure has to be here, and it has to be loud.

THE DELAY KEYS ARE THE PART MOST EASILY GOT WRONG

Every cell that carries a matched delay needs a `BD_SZ_*` override keyed on its
INSTANCE PATH, because verify/resize.sh and verify/teeth.sh drive a design only
by writing those defines and never by editing source.  Get the key right and
the name wrong -- key it on the module, say -- and resize.sh proposes lengths
under a name no source file reads: the tightening loop then reports success
having changed nothing, and every other gate still passes.  bdc/compute.py's
header records that exact failure being reached twice by different routes.

So the module here takes one `parameter DELAY_<inst>` per delay-bearing
instance and the emitted top spells `BD_SZ_UUT_<INST>` for each, matching
verify/tighten.py's own naming (macro('umem.usetup') -> BD_SZ_UMEM_USETUP).
The kernel module stays instance-name-agnostic; only the top, which knows what
it called the thing, spells the key.

Usage:
    python3 bdc/emit.py build/frontend/test_loop_free/comp/handshake_transformed.mlir
"""

import argparse
import heapq
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import compute  # noqa: E402

# Delay elements placed per pipeline stage in front of a SELECT (a cond_br
# condition or a mux control).  Overridable so the value can be swept against
# real hardware instead of argued about: BDC_SELECT_PAD=32 python3 bdc/emit.py ...
SELECT_PAD = int(os.environ.get("BDC_SELECT_PAD", "4"))

def load_select_pads():
    """Per-instance select padding, in bd_delay elements, from a JSON file.

    Set BDC_SELECT_PADS to a path holding {"ulink_n120": 12, ...}.  The
    intended producer is verify/tighten.py run against a routed SDF: it knows
    the actual arrival skew between a select's request and its value on the
    route that was actually built, and a global constant does not.

    Missing file is an ERROR, not a fallback.  Silently reverting to the
    constant would produce a build that looks sized and is not -- the same
    failure mode flow.sh's BD_SIZES comment warns about, where every gate
    passes on a design that ignored its own measurements.
    """
    path = os.environ.get("BDC_SELECT_PADS")
    if not path:
        return {}
    with open(path) as f:
        raw = json.load(f)
    out = {}
    for k, v in raw.items():
        n = int(v)
        if n < 0:
            raise ValueError(f"select pad for {k!r} is negative: {n}")
        out[str(k)] = n
    return out


from hs import parse  # noqa: E402
from map import Table, Unmapped  # noqa: E402


class EmitError(Exception):
    """A construct this emitter will not guess at.  Always names the op."""


# Internal channels to bring out as read-only probe ports.  Set by --probe or
# by BDC_PROBE in the environment, so a build script can turn the probe on
# without the emitter's caller learning a new flag.  See the long comment at
# the probe-port block in emit_func for what a probe is and is not.
PROBE = [p for p in os.environ.get("BDC_PROBE", "").split(",") if p]


# Verilog keywords that a Dynamatic argName/resName can collide with.  `end`
# is not hypothetical: it is the resName of every kernel's completion channel.
RESERVED = {
    "end", "begin", "module", "wire", "reg", "input", "output", "inout",
    "assign", "always", "initial", "parameter", "localparam", "generate",
    "endmodule", "case", "default", "function", "task", "and", "or", "not",
    "buf", "xor", "nand", "nor", "xnor", "if", "else", "for", "while",
}


def vname(ssa):
    """An SSA value name as a Verilog identifier.

    `#` becomes a DOUBLE underscore so that %1#0 and %1_0 -- both of which
    Dynamatic emits -- cannot collide on a single underscore.  emit_func
    asserts the whole mapping is injective rather than trusting this.
    """
    s = ssa.lstrip("%").replace("#", "__")
    s = re.sub(r"[^A-Za-z0-9_]", "_", s)
    return ("n" if s[:1].isdigit() else "n_") + s


def portname(name):
    """A function argName/resName as a Verilog port base."""
    s = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if s in RESERVED or not s[:1].isalpha():
        s = "p_" + s
    return s


def instname(node, index):
    """An instance name, from Dynamatic's own handshake.name where it exists.

    Using their name rather than a counter is not cosmetic: it is what makes a
    BD_SZ key traceable back to a line of MLIR, and what keeps the key stable
    when an unrelated op is added earlier in the function.  A key that moves
    when the graph changes would silently re-point a measured delay length at
    a different cell.
    """
    name = node.attrs.get("handshake.name")
    if isinstance(name, str) and name:
        return "u" + re.sub(r"[^A-Za-z0-9_]", "_", name)
    return f"u{node.op}_{index}"


# ---------------------------------------------------------------------------
# Widths
#
# A channel is (width, is_control).  Control is width 0 and is NOT the same as
# width 1: a control channel has no data net at all, and the bd-config
# convention (W=1, inputs tied low, output dangling) exists precisely so that
# cells needing a width can be handed one without a data net existing.

CONTROL = (0, True)


def _atoms(sig):
    """Every top-level `<...>` in a type clause, decoded.

    `<i32>` -> (32, False);  `<>` -> (0, True).  Anything else raises: an
    unrecognised channel type is exactly the case where guessing a width
    produces a circuit that routes and computes the wrong thing.
    """
    out, depth, start = [], 0, None
    for i, ch in enumerate(sig):
        if ch == "<":
            if depth == 0:
                start = i
            depth += 1
        elif ch == ">":
            depth -= 1
            if depth == 0:
                out.append(sig[start:i + 1])
    decoded = []
    for a in out:
        inner = a[1:-1].strip()
        if inner == "":
            decoded.append(CONTROL)
        elif re.fullmatch(r"i\d+", inner):
            decoded.append((int(inner[1:]), False))
        else:
            raise EmitError(f"unrecognised channel type {a!r} in type clause "
                            f"{sig!r} -- add a rule, do not assume a width")
    return decoded


def _result_atoms(sig):
    """The result half of a type clause: everything after ` to `, if present."""
    parts = re.split(r"\bto\b", sig)
    return _atoms(parts[-1])


def _known(chs):
    """The first operand width that is already resolved, or None.

    A merge, a mux and a cond_br all produce the width their data operands
    carry, and those operands all carry the SAME width -- the IR would be
    ill-typed otherwise.  So any one of them that is already known answers the
    question, and insisting on a particular one is what deadlocks a loop: in
    gcd the first data input of the loop-header mux is the value coming back
    around the loop, whose width is exactly what is being asked for.  Taking
    whichever input is known breaks that ring at the one place it is not
    actually circular -- the input coming in from outside the loop.
    """
    return next((c for c in chs if c is not None), None)


def result_channels(node, operand_ch):
    """The (width, is_control) of each of `node`'s results.

    Explicitly per-op.  A generic rule does not exist -- `cmpi`'s type clause
    spells its OPERAND type and never mentions the i1 it produces, while
    `control_merge`'s spells both results after a `to`.  Anything not listed
    raises by name.

    An entry of `operand_ch` may be None, meaning that operand's width is not
    known yet.  A rule that needs it returns None in that result's place and
    the caller tries again later; a rule that does not need it -- and several
    genuinely do not -- answers straight away.  Returning None is NOT a way to
    express "unknown width": it means "ask me again", and the fixpoint fails
    loudly if the answer never arrives.
    """
    op = node.op
    nres = len(node.results)

    if op in ("fork", "lazy_fork"):
        return [operand_ch[0]] * nres
    if op == "source":
        return [CONTROL]
    if op == "constant":
        value = node.attrs.get("value")
        t = getattr(value, "type", None)
        if isinstance(t, str) and re.fullmatch(r"[iu]\d+", t):
            return [(int(t[1:]), False)]
        return [_result_atoms(node.type_sig)[-1]]
    if op == "cmpi":
        return [(1, False)]
    if op in ("addi", "subi", "muli", "andi", "ori", "xori",
              "shli", "shrsi", "shrui"):
        return [operand_ch[0]]
    if op == "select":
        return [operand_ch[1]]
    if op == "cond_br":
        return [operand_ch[1], operand_ch[1]]
    if op in ("br", "buffer"):
        return [operand_ch[0]]
    if op == "merge":
        return [_known(operand_ch)]
    if op in ("trunci", "extui", "extsi"):
        # `trunci %19 : <i32> to <i1>` -- the width that matters is the one
        # after the `to`, and it is the only place it appears.  These are the
        # ops bdc/compute.py's header deliberately refuses: a slice or a
        # concatenation is wire, not logic, so it is lowered here and gets no
        # compute unit and no matched delay.
        return [_result_atoms(node.type_sig)[-1]]
    if op == "mux":
        return [_known(operand_ch[1:])]
    if op == "control_merge":
        atoms = _result_atoms(node.type_sig)
        if len(atoms) != 2:
            raise EmitError(f"control_merge type clause {node.type_sig!r} did "
                            f"not yield a (result, index) pair")
        return atoms
    if op in ("sink", "end"):
        return []
    if op == "join":
        return [CONTROL]
    raise EmitError(f"no width rule for handshake op {op!r} -- add one to "
                    f"result_channels(), do not assume")


# ---------------------------------------------------------------------------
# Generated helper cells
#
# The arbitrated merge is not a cell in cells/rtl/ and cannot be: the library
# is frozen, and what is needed is a composition of three cells that already
# exist.  bdc/AUDIT.md section 1 fixes the composition -- "a data-carrying
# arbitrated merge adds bd_merge's select LUT, data mux and matched delay on
# R0" -- and the arbiter's own header fixes why bd_merge itself is the wrong
# cell to stack on top: bd_arbiter ALREADY merges the two requests (R0 = g1 +
# g2) and already returns both acknowledges (A1 = C(g1,A0)), so putting a
# bd_merge behind it would acknowledge every token twice.

AMERGE_HEADER = """
// ---------------------------------------------------------------------------
// bdc_amerge -- two channels in, one out, arbitrated.
//
// handshake.merge does NOT promise its inputs are exclusive and bd_merge
// REQUIRES it, so every multi-input merge gets an arbiter.  Unconditionally:
// bdc/AUDIT.md section 1 records the decision not to prove exclusivity and
// skip it, on the owner's call, with the exposure measured in
// cells/verify/MTBF.md taken as sufficient.
//
//     bd_arbiter    r1/r2 -> R0, and the two acknowledges
//     bd_datamux    the winner's data, selected by the grant
//     uor + udly    the matched delay that makes the data valid before R0
//
// The grants are levels off the same state node R0 is a function of, so g2
// and R0 leave the arbiter together and the mux output is NOT valid when R0
// rises.  That is what the delay is for, and it is the whole bundling
// obligation of this cell.
//
// `uor` is a pass-through LUT1 and it is load-bearing: verify/tighten.py
// finds the cells it must audit by looking for `<cell>.uor`, and its own
// comment says why keying off the delay chain instead was wrong -- bd_delay
// #(.N(0)) is a bare wire, so the cell that most needs auditing would leave
// nothing in the netlist to find and be skipped in silence.  It costs
// nothing: a LUT1 in front of a LUT1 chain is one more link of that chain,
// so DELAY is one shorter to compensate.
// ---------------------------------------------------------------------------
"""


def _ports(n, dw, kind):
    """The N repeated channel ports, as Verilog text."""
    pad = "     " if dw > 9 else "      "
    out = []
    for k in range(n):
        out.append(f"""     input  wire             {kind}{k}_req,
     output wire             {kind}{k}_ack,
     input  wire [{dw - 1}:0]{pad}{kind}{k}_data,
""")
    return "\n".join(out)


def _index_expr(n, sig):
    """Winner index from the per-stage grants, as a priority chain.

    Stage k's grant is only meaningful when no LATER stage won, because a
    later stage that granted is still holding its A0 low and stage k's own
    grant is whatever it was when it last fired.  Reading them newest-first
    is what makes the stale ones unreachable rather than merely unlikely.
    """
    iw = max(1, (n - 1).bit_length())
    expr = f"{iw}'d0"
    for k in range(1, n):
        expr = f"{sig}[{k}] ? {iw}'d{k} : ({expr})"
    return iw, expr


def _data_mux(n, dw, sel, name):
    """z_data as a chain of conditionals on `sel`."""
    expr = f"{name}0_data"
    for k in range(1, n):
        expr = f"({sel} == {k}) ? {name}{k}_data : ({expr})"
    return expr


def emit_amerge(width, n=2):
    """The N-input arbitrated data merge, as a module.

    N inputs is a CASCADE of two-input bd_arbiters, not a balanced tree: each
    stage arbitrates the accumulated winner so far against one more input, so
    stage k's R0/A0 is stage k+1's r1/A1.  A cascade because that is the shape
    whose grant decoding is a priority chain over the stage grants -- a
    balanced tree needs the same number of arbiters and gives an encoding that
    is harder to argue about, for a fairness gain that is not measured
    anywhere and is not what this cell is for.

    At n=2 this reduces to exactly one bd_arbiter with index = g2, which is
    the circuit that was here before N inputs existed.

    Fairness across the cascade is deliberately not claimed: input 0 goes
    through every stage and input n-1 through one, so a saturated input n-1
    can starve input 0.  handshake.merge makes no fairness promise for this to
    violate, and the graphs this backend sees have at most three predecessors
    on a control_merge.  If a kernel ever depends on it, that is a design
    question and it should be answered deliberately, not by quietly changing
    the topology here.
    """
    dw = max(width, 1)
    pad = "     " if dw > 9 else "      "
    iw, idx_expr = _index_expr(n, "won")
    won_lines = "\n".join(
        f"    assign won[{k}] = g2[{k}] | in{k}_ack;" for k in range(1, n))

    stages = []
    acc_req, acc_ack = "in0_req", "in0_ack"
    for k in range(1, n):
        last = (k == n - 1)
        r0 = "r0" if last else f"acc{k}_req"
        a0 = "z_ack" if last else f"acc{k}_ack"
        if not last:
            stages.append(f"    wire {r0}, {a0};")
        stages.append(f"""    bd_arbiter uarb{k} (
        .rst(rst),
        .r1({acc_req}), .A1({acc_ack}),
        .r2(in{k}_req), .A2(in{k}_ack),
        .R0({r0}),{' ' * max(1, 8 - len(r0))}.A0({a0}),
        .g1(g1[{k}]),  .g2(g2[{k}]));""")
        acc_req, acc_ack = r0, a0

    return AMERGE_HEADER + f"""
(* keep_hierarchy *)
module bdc_amerge{n}_{width} #(parameter DELAY = 4)
    (input  wire             rst,

{_ports(n, dw, "in")}
     output wire             z_req,
     input  wire             z_ack,
     output wire [{dw - 1}:0]{pad}z_data,

     output wire [{iw - 1}:0]{pad}index);

    wire r0;
    wire [{n - 1}:1] g1, g2;

{chr(10).join(stages)}

    // Which input won, as ordinary channel data -- and NOT the bare grant.
    //
    // cells/rtl/bd_merge.v states the rule this obeys, and states it as the
    // reason it does not select on the request:
    //
    //     "The select cannot be the request.  Selecting on x_req flips the
    //      mux the moment x enters phase three, while the downstream latch is
    //      still transparent.  The select must rise with the request and fall
    //      with the ack."
    //
    // g2 IS effectively the request here: g2 = r2 . ~q, so it falls when the
    // input request falls, which is when R0 falls -- and A0, the ack that
    // ends the downstream latch's hold window, falls strictly later.  That
    // leaves a window where this cell is still being read and has already
    // stopped saying who won.  bd_link's own header is explicit that its data
    // must hold until ACK-fall and not req-fall.
    //
    // g2 | ack is bd_merge's `x_req + x_ack` written for a grant: it rises
    // with the grant and falls only once the acknowledge has gone too.
    wire [{n - 1}:1] won;
{won_lines}
    assign index = {idx_expr};

    assign z_data = {_data_mux(n, dw, "index", "in")};

    wire either;
    (* keep *) LUT1 #(.INIT(2'h2)) uor (.I0(r0), .O(either));
    bd_delay #(.N(DELAY)) udly (.a(either), .z(z_req));

    // g1 is read so the arbiter's own output cannot be optimised away; the
    // grants are a fractured pair and deleting one changes the cell that
    // cells/verify/MTBF.md characterised.
    wire unused_g1 = |g1;
endmodule
"""


MUXN_HEADER = """
// ---------------------------------------------------------------------------
// bdc_muxn -- N channels in, one out, picked by an index channel.
//
// cells/rtl/bd_mux.v generalised from two inputs to N.  Its structure is kept
// exactly, because its correctness argument is about the SHAPE and not about
// the arity:
//
//     j_k    = C(in_k_req, ctl_req . (s == k))
//     z_req  = delta(OR of all j_k)
//     in_k_ack = C(j_k, z_ack)
//     ctl_ack  = z_ack
//     z_data   = in_s_data
//
// Only the selected input is acknowledged, because in_k_ack can only rise if
// j_k fired and j_k can only fire if the index said k.  Every other input
// keeps its token untouched, which is what a loop header needs.
//
// WHY THIS IS NOT A TREE OF bd_mux, which is the obvious thing to try and is
// wrong: a tree needs the index at every level, so the index channel has to
// be forked.  A fork does not complete until every branch acknowledges, and
// the branch feeding a level that the index did not select never fires -- so
// it never acknowledges, and the fork deadlocks.  The one-level form has one
// consumer of the index and cannot deadlock that way.
//
// bd_mux folds its decode into the join's LUT6, which at two inputs is free
// because ~s and s are one wire.  At N inputs the decode is a comparison
// against a multi-bit index and does not fit, so it is left as ordinary logic
// for yosys to map.  That is safe for the same reason bd_mux's own comment
// gives for trusting s: the index is ordinary channel data, held by the
// control channel's contract from ctl_req-rise to ctl_ack-fall, so the decode
// is a monotonic function of ctl_req over a window where everything else it
// reads is already stable.  It cannot glitch a join input high.
//
// The OR feeding the delay cannot glitch either: the decode is one-hot, so at
// most one j_k is ever changing.
// ---------------------------------------------------------------------------
"""


def emit_muxn(width, n):
    """The N-input index-selected mux, as a module."""
    dw = max(width, 1)
    pad = "     " if dw > 9 else "      "
    iw = max(1, (n - 1).bit_length())

    joins = []
    for k in range(n):
        joins.append(
            f"    assign sel[{k}] = ctl_req & (s == {iw}'d{k});\n"
            f"    bd_c2 uj{k} (.a(in{k}_req), .b(sel[{k}]), .rst(rst), "
            f".q(j[{k}]));")
    acks = "\n".join(
        f"    bd_c2 ua{k} (.a(j[{k}]), .b(z_ack), .rst(rst), "
        f".q(in{k}_ack));" for k in range(n))

    return MUXN_HEADER + f"""
(* keep_hierarchy *)
module bdc_muxn{n}_{width} #(parameter DELAY = 4)
    (input  wire             rst,

{_ports(n, dw, "in")}
     input  wire             ctl_req,
     output wire             ctl_ack,
     input  wire [{iw - 1}:0]{pad}s,

     output wire             z_req,
     input  wire             z_ack,
     output wire [{dw - 1}:0]{pad}z_data);

    wire [{n - 1}:0] sel, j;

{chr(10).join(joins)}

    wire either;
    (* keep *) LUT1 #(.INIT(2'h2)) uor (.I0(|j), .O(either));
    bd_delay #(.N(DELAY)) udly (.a(either), .z(z_req));

{acks}

    assign ctl_ack = z_ack;

    assign z_data = {_data_mux(n, dw, "s", "in")};
endmodule
"""


# ---------------------------------------------------------------------------
# Storage placement
#
# THIS IS A POLICY AND IT IS EXPECTED TO CHANGE.  It is isolated in one
# function so that changing it is a change to one function.
#
# Dynamatic's --handshake-place-buffers is the pass we deliberately do not run
# (COMPILER-PLAN.md cuts immediately above it: it is a MILP against a target
# clock period, and there is no clock).  So the graph arrives with no storage
# on any channel, and something here has to put it back.
#
# bdc/slack.py already covers one reason to need storage -- a cycle with none
# is a combinational loop and no routing saves it.  This is a SECOND and
# independent reason, found by routing the first emitted kernel and asking
# verify/tighten.py the only question that matters for bundled data: does each
# cell's request come out AFTER that cell's own data?  For 7 of 9 matched
# delays it could not answer, all with the same shape.
#
#     uut.uaddi0   8 links   req 0  peak 3701  guard 740  margin -4441
#                  paired as one bundled channel (no common source):
#                    request from uut.uaddi0.udly.chain.g[7].u/O6
#                    data    from upipe.many.lat[3].u.pair[42].u$LUT5/O5
#
# Both halves are arrival times, and they were measured from different places,
# so subtracting them means nothing.  The request's clock starts at the cell's
# own join C-element, because a C-element is a feedback loop and an arrival
# time cannot be carried through one.  The data's clock starts 3.7 ns earlier,
# at the last latch upstream, because nothing cut that path at all.  The
# analysis says so rather than staying quiet, which is the right call -- a
# delay that was never checked looks exactly like a delay that passed.
#
# A bd_link on the channel fixes both halves at once.  The data then leaves the
# link's latch and the request leaves the link's delay, and both start from the
# link's own control node -- so the cell's delay becomes a local quantity that
# can be measured, instead of an accumulation across everything upstream of it.
#
# The rule below is the narrowest one that does that: storage in front of the
# cells that carry a matched delay, and nowhere else.  Every other channel
# stays wire, and wire is free.

# Ops that instantiate a cell carrying a matched delay -- i.e. the ops whose
# data inputs have to arrive from a known start point for rule A to work.
DELAY_BEARING = {
    "addi", "subi", "muli", "cmpi", "andi", "ori", "xori",
    "shli", "shrsi", "shrui", "select", "mux",
}


# ---------------------------------------------------------------------------
# BDC_CONST_FOLD -- fuse a maximal region of purely combinational arithmetic
# into ONE generated cell, instead of one cell (one keep_hierarchy boundary,
# one bd_join, one matched delay, one storage stage) per op.
#
# The problem this fixes is not really "constants cost too much": a constant
# operand passed as a full handshake channel hides its own value from yosys
# behind a keep_hierarchy boundary, so `x << 13` synthesises as a general
# 32-bit barrel shifter instead of wiring.  But that is a SYMPTOM of the
# coarser problem, which is that this backend lowers one handshake op to one
# cell no matter how small the op is or how directly it feeds the next one --
# so xorshift's loop body, about 3 LUT levels of real logic (three constant
# shifts and three XORs), pays for 6 sealed module boundaries, 3 fork/join
# pairs and 7 handshake stages on its ring.  Fusing the region fixes both at
# once: constants land inside the one remaining boundary, where yosys folds
# them for free, and the redundant interior joins disappear because they were
# rendezvousing branches of the SAME transaction that were never going to
# arrive apart.
#
# What must NOT be fused across is anything that is not combinational: a
# buffer, a mux/control_merge/cond_br (real control flow, whose branches
# really can arrive apart), a memory op, or anything else that carries its
# own handshake state.  FUSABLE_OPS is DELAY_BEARING minus "mux" for exactly
# this reason -- "mux" is an ARBITRATED n-way rendezvous over control that can
# come from a different iteration than its data (see _op_mux), not a wire-
# level expression, and fusing across it would dissolve a real boundary
# rather than a redundant one.
#
# This does NOT cost auditability, which is the reason keep_hierarchy and
# rule 1 (measurability_sites) exist in the first place.  A fused cell still
# has exactly one keep_hierarchy boundary and one matched delay, sized off
# the one storage stage in front of it -- there are just fewer delays to size
# and check, not a boundary removed from checking.
#
# NOW DEFAULT ON.  It was default OFF for two reasons and both are spent.
#
# The first was that the single-consumer premise fusion rests on was asserted
# in a comment rather than checked, so a graph that broke it would have been
# mis-emitted silently.  That is fixed and has a negative control in
# test_fusion_sharing.py.
#
# The second was that a default-on change would silently alter a build someone
# else had in flight.  That is a real cost, and it is smaller than what
# staying off costs: on xorshift, folding is the difference between 12 and 15
# delay-bearing cells, because `x ^= x << 13` becomes a full handshake cell
# with its own matched delay when a constant shift is nothing but rewiring.
# Measured through the default path, that is 82.4 ns of built matched delay
# against 33.4 ns -- and the 33.4 ns build is the one every speedup on this
# board was measured from.  Leaving it off meant the default build was 2.5x
# looser than the numbers being quoted for it.
#
# Read once at module scope, same convention as BDC_SELECT_PAD/BDC_RING_PAD.
# Set BDC_CONST_FOLD=0 for the unfused lowering.
BDC_CONST_FOLD = os.environ.get("BDC_CONST_FOLD", "1") == "1"

# Ops safe to fuse across: DELAY_BEARING minus "mux" -- see the block comment
# above for why "mux" is excluded.
FUSABLE_OPS = DELAY_BEARING - {"mux"}

# Channel-position map for each fusable op.  Exactly _bind_compute's mapping,
# duplicated here (rather than imported from it) because fusion analysis has
# to walk operands before any Emitter, and before any per-op cell, exists.
_FUSABLE_CHANS = {
    op: ({"s": 0, "a": 1, "b": 2} if op == "select" else {"a": 0, "b": 1})
    for op in FUSABLE_OPS
}

# How many arithmetic ops one fused cell may absorb.  A FIXED bound, not a
# measured one: link_sites()'s docstring already names "storage where the
# uncut combinational depth exceeds a threshold" as an alternative to rule 1
# and rejects it for needing a route to decide -- but cells/verify/converge.sh
# and resize.sh already ARE that iterate-until-it-passes loop, so the
# objection is against building an unbounded fuser with no way to size its
# own delay, not against a bound at all.  This pass does not build that
# feedback loop; it picks a small conservative bound instead and leaves
# closing it on measurement for later.  4 covers every region actually seen
# in xorshift and collatz (2 ops each) with room to spare.
MAX_FUSE_NODES = 4


class _UnionFind:
    """Union-find with a hard cap on merged component size."""

    def __init__(self, items):
        self.parent = {i: i for i in items}
        self.size = {i: 1 for i in items}

    def find(self, x):
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union_if(self, a, b, cap):
        """Merge a's and b's components iff the result is <= cap.  Returns
        whether they ended up in the same component (True if they already
        were, whether or not this call did anything)."""
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return True
        if self.size[ra] + self.size[rb] > cap:
            return False
        self.parent[rb] = ra
        self.size[ra] += self.size[rb]
        return True


class Region:
    """One fused combinational region.

    `node_ids` is every member, func.nodes indices, in topological order.
    `anchor` is the sink: the one member whose result leaves the region (see
    _build_region for why there is guaranteed to be exactly one).
    `ext_inputs` is the region's true external operands, in first-encountered
    order -- these are the only channels that get a bd_join branch.
    `ref[(node_id, port)]` says how that node's operand is wired:
    `("const", value)` for a folded literal, `("ext", k)` for
    `ext_inputs[k]`, `("wire", producer_id)` for another member's result.
    """

    def __init__(self, node_ids):
        self.node_ids = node_ids
        self.anchor = None
        self.ext_inputs = []
        self.const_of = {}
        self.ref = {}


class FusionPlan:
    """compute_fusion()'s answer for one handshake.func.

    `skip` is every node index emit_func's driver loop must NOT lower
    individually: absorbed (source, constant) pairs, and every fused region
    member except its anchor.  `anchor_region` maps a region's anchor index
    to its Region, which is where the driver loop instantiates the whole
    fused cell.  `dead_values` is every SSA result that ends up with no net
    at all in the emitted module -- decls and --probe both have to know not
    to reference one.
    """

    def __init__(self):
        self.skip = set()
        self.region_of = {}
        self.anchor_region = {}
        self.dead_values = set()


def _topo_order(nodes, members, value_producer, member_set):
    """`members`, ordered so every node follows every in-region producer of
    its operands.  A plain DFS postorder: fusable regions cannot contain a
    cycle (a cycle needs a mux/control_merge to close, and those are never
    fusable), so this always terminates and is always a valid order."""
    deps = {}
    for i in members:
        d = []
        for opnd in nodes[i].operands:
            p = value_producer.get(opnd)
            if p in member_set:
                d.append(p)
        deps[i] = d
    order, visited = [], set()

    def visit(i):
        if i in visited:
            return
        visited.add(i)
        for d in deps[i]:
            visit(d)
        order.append(i)

    for i in sorted(members):
        visit(i)
    return order


def _build_region(func, members, value_producer, value_consumers, const_of):
    nodes = func.nodes
    member_set = set(members)
    region = Region(_topo_order(nodes, members, value_producer, member_set))

    # --handshake-materialize guarantees one consumer per SSA value (see this
    # file's own header), and every FUSABLE_OPS node has exactly one result
    # (checked below).  So every member's out-edge either stays inside the
    # region (its single consumer is another member) or leaves it -- and a
    # member cannot do both.  Two members leaving would need one of them to
    # be reachable from the other AND from outside, which the single-consumer
    # guarantee forbids; so this set has exactly one member in it whenever the
    # guarantee holds.  Asserted, not assumed: if some future op breaks the
    # premise, this must fail loudly rather than silently drop a result.
    sinks = []
    for i in region.node_ids:
        if len(nodes[i].results) != 1:
            raise EmitError(
                f"BDC_CONST_FOLD: fusable op {nodes[i].op!r} at line "
                f"{nodes[i].src_line} has {len(nodes[i].results)} results, "
                f"not the 1 every FUSABLE_OPS lowering assumes")
        # A member is a sink if ANY consumer of its result sits outside the
        # region -- or if nothing consumes it at all, which is still a result
        # that has to leave.  Asking only about the first consumer was how an
        # externally-read value could be mistaken for an internal one.
        eaters = value_consumers.get(nodes[i].results[0], [])
        if not eaters or any(c not in member_set for c in eaters):
            sinks.append(i)
    if len(sinks) != 1:
        raise EmitError(
            f"BDC_CONST_FOLD: fused region "
            f"{[nodes[i].op for i in region.node_ids]} has {len(sinks)} "
            f"external result(s), expected exactly 1 -- the single-consumer "
            f"guarantee --handshake-materialize gives every value does not "
            f"hold here, and fusion cannot assume a single external output")
    region.anchor = sinks[0]

    region.const_of = {(i, port): v for (i, port), v in const_of.items()
                        if i in member_set}

    ext_index = {}
    for i in region.node_ids:
        n = nodes[i]
        for port, pos in _FUSABLE_CHANS[n.op].items():
            if (i, port) in region.const_of:
                region.ref[(i, port)] = ("const", region.const_of[(i, port)])
                continue
            opnd = n.operands[pos]
            p = value_producer.get(opnd)
            if p in member_set:
                region.ref[(i, port)] = ("wire", p)
                continue
            if opnd not in ext_index:
                ext_index[opnd] = len(region.ext_inputs)
                region.ext_inputs.append(opnd)
            region.ref[(i, port)] = ("ext", ext_index[opnd])

    if not region.ext_inputs:
        # Every operand of every node in this region folded to a literal, so
        # there is nothing left to drive the join's request -- the region
        # would never fire.  Expected to never trigger on a real kernel (the
        # frontend already constant-folds const-op-const before this backend
        # ever sees it), so this is a safety net, not a measured path: un-fold
        # ONE constant back into a live channel rather than emit a cell with
        # no way to start.
        (i, port) = next(iter(region.const_of))
        del region.const_of[(i, port)]
        opnd = nodes[i].operands[_FUSABLE_CHANS[nodes[i].op][port]]
        region.ext_inputs.append(opnd)
        region.ref[(i, port)] = ("ext", 0)

    return region


def compute_fusion(func):
    """BDC_CONST_FOLD's whole analysis: which nodes fuse, which constants
    fold.  Pure graph analysis -- no widths needed, so this can run before
    Emitter._resolve_widths, and does not depend on the Emitter at all.
    """
    nodes = func.nodes
    value_producer = {}
    for i, n in enumerate(nodes):
        for r in n.results:
            value_producer[r] = i
    # EVERY consumer, not just the first one seen.  This used to be a
    # setdefault into a value->consumer map, which silently kept whichever
    # consumer happened to come first in node order and threw the rest away.
    # Both places that read it are load-bearing, and both break quietly:
    #
    #   the sink test in _build_region asks whether a member's result leaves
    #   the region.  With a first-consumer map, a value read by one node
    #   INSIDE the region and one OUTSIDE looks purely internal whenever the
    #   inside reader sorts first -- so the region emits without that output
    #   and the outside reader's channel is dropped;
    #
    #   constant absorption asks who eats a constant.  A constant feeding two
    #   nodes gets absorbed into the first and deleted, stranding the second.
    #
    # The premise both rely on is that --handshake-materialize gives every
    # value exactly one consumer, inserting a `fork` wherever a value is read
    # twice.  That premise was never checked; it was spelled out in a comment
    # and then assumed.  Check it, because fusion is only sound while it holds
    # and because BDC_CONST_FOLD is now something a default build can turn on.
    value_consumers = {}
    for i, n in enumerate(nodes):
        for o in n.operands:
            value_consumers.setdefault(o, []).append(i)

    fusable = {i for i, n in enumerate(nodes) if n.op in FUSABLE_OPS}

    # -- constant absorption ------------------------------------------------
    # A constant folds into whichever fusable node it feeds ONLY when its own
    # control token comes from a bare `source` -- i.e. only when eliding the
    # constant's live channel cannot strand anything else waiting on it.
    # Dynamatic emits exactly this shape for every literal operand (one
    # `source` per `constant`, feeding nothing else -- checked, not assumed,
    # against build/frontend/xorshift's handshake_transformed.mlir); a
    # constant fed by anything else is left as an ordinary live channel.
    absorbed = set()
    const_of = {}
    for i, n in enumerate(nodes):
        if n.op != "constant":
            continue
        eaters = value_consumers.get(n.results[0], [])
        # Exactly one.  Absorbing a constant deletes its channel, so a second
        # reader would be left waiting on a wire nobody drives.
        if len(eaters) != 1:
            continue
        consumer = eaters[0]
        if consumer not in fusable:
            continue
        ctl_producer = value_producer.get(n.operands[0])
        if ctl_producer is None or nodes[ctl_producer].op != "source":
            continue
        value = n.attrs.get("value")
        raw = getattr(value, "value", value)
        if not isinstance(raw, int):
            continue
        chans = _FUSABLE_CHANS[nodes[consumer].op]
        port = next((p for p, pos in chans.items()
                     if nodes[consumer].operands[pos] == n.results[0]), None)
        if port is None:
            continue
        const_of[(consumer, port)] = raw
        absorbed.add(i)
        absorbed.add(ctl_producer)

    # -- region grouping ------------------------------------------------------
    # Union nodes across every direct fusable-to-fusable edge, in a
    # deterministic order, capped so no component exceeds MAX_FUSE_NODES.
    uf = _UnionFind(fusable)
    edges = []
    for i in fusable:
        for opnd in nodes[i].operands:
            p = value_producer.get(opnd)
            if p is not None and p in fusable:
                edges.append((opnd, p, i))
    edges.sort(key=lambda e: e[0])
    for _, p, c in edges:
        uf.union_if(p, c, MAX_FUSE_NODES)

    groups = {}
    for i in fusable:
        groups.setdefault(uf.find(i), []).append(i)

    plan = FusionPlan()
    plan.skip |= absorbed
    for members in groups.values():
        region = _build_region(func, members, value_producer, value_consumers,
                                const_of)
        for i in region.node_ids:
            plan.region_of[i] = region
            if i != region.anchor:
                plan.skip.add(i)
                plan.dead_values.add(nodes[i].results[0])
        plan.anchor_region[region.anchor] = region
    for i in absorbed:
        plan.dead_values.add(nodes[i].results[0])
    return plan


def _fused_node_expr(op, width, pred, ports, uniq):
    """One interior node's RHS expression inside a fused region.

    The same per-op logic bdc/compute.py's emit_unit uses for a standalone
    cell -- deliberately kept as a separate copy rather than shared with it,
    so that touching this (BDC_CONST_FOLD-only) path can never change what
    emit_unit produces on the default, flag-off path.  `ports` maps
    'a'/'b'/'s' to already-resolved Verilog text (a literal, an external
    port net, or another node's interior wire); `uniq` disambiguates
    internal wire names between nodes sharing one fused module.
    """
    extra = []
    if op == "cmpi":
        if pred not in compute.CMPI:
            raise EmitError(f"unknown cmpi predicate {pred!r}")
        flip = None
        if pred in compute.SIGNED_CMPI:
            flip = "1'b1" if width == 1 else f"{{1'b1, {width - 1}'b0}}"
        xa, xb = f"xa_{uniq}", f"xb_{uniq}"
        extra.append(f"    wire [{width - 1}:0] {xa} = {ports['a']}"
                     + (f" ^ {flip};" if flip else ";"))
        extra.append(f"    wire [{width - 1}:0] {xb} = {ports['b']}"
                     + (f" ^ {flip};" if flip else ";"))
        tmpl = compute.CMPI[pred]
        g = e = None
        if "{g}" in tmpl:
            g = f"cmp_g_{uniq}"
            extra.append(f"    wire {g} = {xa} > {xb};")
        if "{e}" in tmpl:
            e = f"cmp_e_{uniq}"
            extra.append(f"    wire {e} = {xa} == {xb};")
        expr = tmpl.format(g=g, e=e)
        out_w = 1
    elif op == "select":
        # No `[0]` bit-select here, unlike compute.emit_unit's `s_data[0]` --
        # that indexes into a port declared `[0:0]` on purpose so a width-1
        # channel can still be handed to a cell needing a range.  A fused
        # region's `s` may instead be a bare literal or another node's
        # unranged 1-bit wire (see the cmpi branch above), and iverilog
        # rejects a bit-select on either.  `s` is already exactly 1 bit
        # everywhere it can come from, so using it whole is both simpler and
        # correct.
        expr = f"{ports['s']} ? {ports['a']} : {ports['b']}"
        out_w = width
    elif op in compute.BINARY:
        expr = compute.BINARY[op].format(a=ports["a"], b=ports["b"])
        out_w = width
    else:
        raise EmitError(f"BDC_CONST_FOLD has no fused lowering for {op!r}")
    return extra, expr, out_w


# Where a cycle-breaking link goes, when the cycle offers a choice.  A loop
# header is the natural rest position for a loop-carried token: it is the one
# node in the cycle that already has an input from OUTSIDE the loop, so the
# link starts empty, takes the entry token on the first iteration, and holds
# each subsequent one exactly where the next iteration expects to find it.
HEADER_OPS = ("control_merge", "merge", "mux")


def measurability_sites(func, channels):
    """Rule 1: storage in front of every cell that carries a matched delay.

    See the block comment above.  This rule exists so verify/tighten.py can
    measure a delay against a known start point, and it deliberately skips
    control channels -- a channel with no data has no data to arrive early,
    so re-timing it buys nothing rule A can use.
    """
    sites = set()
    const = {r for n in func.nodes if n.op == "constant" for r in n.results}
    for node in func.nodes:
        multi = node.op in ("merge", "control_merge") and len(node.operands) >= 2
        if node.op not in DELAY_BEARING and not multi:
            continue
        for o in node.operands:
            width, _is_control = channels[o]
            if width == 0:
                continue        # no data, so nothing can be early
            if o in const:
                # A constant's data is a literal.  It is valid before the
                # circuit powers on, never mind before the request arrives,
                # so re-timing it buys nothing and costs a latch per bit.
                continue
            sites.add(o)
    return sites


def measurability_sites_fused(func, channels, fusion):
    """Rule 1 under BDC_CONST_FOLD: storage in front of a fused region's
    EXTERNAL inputs, instead of in front of every arithmetic op's own
    operands.

    Interior edges of a region are no longer channels at all -- they are
    plain Verilog wires inside one cell -- so putting rule 1's storage on
    them would be wrong twice over: there is no port left to put a bd_link
    on, and there is nothing left for tighten.py to measure a matched delay
    against (the interior logic has no delay of its own; the region's one
    matched delay already covers it).  Any op fusion leaves untouched --
    today just `mux` -- keeps rule 1 exactly as measurability_sites() has it.
    """
    sites = set()
    const = {r for n in func.nodes if n.op == "constant" for r in n.results}
    for node in func.nodes:
        multi = node.op in ("merge", "control_merge") and len(node.operands) >= 2
        bearing = (node.op in DELAY_BEARING and node.op not in FUSABLE_OPS) or multi
        if not bearing:
            continue
        for o in node.operands:
            width, _is_control = channels[o]
            if width == 0 or o in const:
                continue
            sites.add(o)
    for region in fusion.anchor_region.values():
        for o in region.ext_inputs:
            width, _is_control = channels[o]
            if width == 0 or o in const:
                continue
            sites.add(o)
    return sites


def cycle_sites(func, already):
    """Rule 2: enough further links that no cycle is left without storage.

    This is COMPILER-PLAN Stage 5 obligation 3, the one bdc/slack.py reports
    and nothing acted on.  It is a SEPARATE rule from rule 1 above and it has
    to be, because the two disagree exactly where it matters:

    Rule 1 skips width-0 channels, correctly, for its own purpose.  gcd's loop
    headers are sequenced by pure CONTROL rings -- control_merge2 -> cond_br22
    -> straight back into control_merge2, every edge width 0 -- so rule 1 puts
    nothing in them at all.  On gcd rule 1 links 123 channels and leaves four
    such rings, and a handshake ring with no storage cannot advance: every
    cell in it routes its request combinationally, so the ring's request is a
    function of itself and there is nowhere for the loop-carried token to
    rest.  That is what made gcd time out on any vector needing a real
    iteration, while the two early-exit vectors -- which never close a loop --
    passed.

    Rather than trust one pass, cut and re-run: link one edge, rebuild the
    residual graph, ask Tarjan's again, and stop when no cycle survives.  A
    single sweep would be wrong because one link can break several overlapping
    cycles at once, and re-running is how you find out that it did instead of
    paying for a link per cycle.
    """
    # bdc is imported both as a package (bdc.emit) and as loose modules on
    # sys.path (simcheck.py does the latter), so take whichever works.
    try:
        from . import slack
    except ImportError:
        import slack

    edges, _adj = slack.build_node_graph(func)
    ids = list(range(len(func.nodes)))
    linked = set(already)
    sites = set()

    while True:
        radj = {v: [] for v in ids}
        for e in edges:
            if e.value not in linked:
                radj[e.producer].append(e.consumer)
        live = [c for c in slack.tarjan_scc(ids, radj) if slack._is_cycle(c, radj)]
        if not live:
            return sites
        for comp in live:
            members = set(comp)
            cand = [e for e in edges
                    if e.producer in members and e.consumer in members
                    and e.value not in linked]
            if not cand:
                raise EmitError(
                    f"{func.name}: cycle through "
                    f"{[slack.node_label(func, v) for v in comp]} has no "
                    f"unlinked edge left to break -- storage cannot fix it")
            # Deterministic, and biased to the loop header.  Sorting by SSA
            # name makes the choice independent of dict/set iteration order,
            # so the same .mlir always emits the same Verilog.
            cand.sort(key=lambda e: (
                func.nodes[e.consumer].op not in HEADER_OPS, str(e.value)))
            pick = cand[0]
            linked.add(pick.value)
            sites.add(pick.value)


# How many storage stages a cycle needs before a token can actually go round
# it.  THREE, and the number is measured, not argued -- cells/tb/tb_ring.v
# sweeps it on the frozen cells and gcd's own loop shape confirms it.
#
# Two stages are not enough and the reason is structural.  Close a ring of the
# simple Muller controller, c_i = C(c_i-1, ~c_i+1), on two stages and each
# controller's two inputs become x and ~x -- permanently disagreeing, so a
# C-element holds, from every state, forever.  Said the other way round:
# occupancy is half a token per stage (rtl/bd_link.v), so one token already
# fills two stages and needs a third to move into.
#
# Nothing else in a cycle counts toward this.  A mux, a steer, a fork, a join
# is a per-transaction rendezvous that returns to zero every cycle -- it can
# pass a token through but cannot hold one, so it adds no stages.  Measured
# directly on the mux -> steer -> storage -> mux ring: one and two stages dead,
# three and up live, with the mux and steer contributing nothing.
RING_MIN_STAGES = 3

_INF = float("inf")


def ring_depths(func, linked):
    """How deep each link has to be, so that every cycle clears RING_MIN_STAGES.

    Returns {ssa: n_stages}, defaulting to 1 -- a plain bd_link -- and deeper
    only where some cycle through that channel would otherwise be under the
    floor.  Depth is added at ONE point per short cycle rather than spread
    around it: three stages in a single bd_pipe circulate exactly as well as
    three scattered ones, and cost the same, so there is no reason to prefer
    the fiddlier placement.

    The floor has to hold on every SIMPLE CYCLE, which is why this works on
    shortest paths rather than on SCCs.  Counting stages per SCC is the
    tempting cheap version and it is wrong in exactly the way that matters: on
    gcd, the SCC holding the main loop carries 34 stages and still contains
    control_merge2 -> cond_br22 -> control_merge2 with ONE.  Summing over a
    component says that ring is fine; it deadlocks anyway.

    So: weight each edge by the stages on it, find the lightest cycle in the
    whole graph, and if it is under the floor, deepen a link on it.  Repeat.
    The lightest cycle is `min over edges (u,v) of w(u,v) + dist(v -> u)`,
    which is all-pairs shortest paths -- cheap here because the weights are
    small non-negative ints and the graphs are a few hundred nodes.
    """
    try:
        from . import slack
    except ImportError:
        import slack

    edges, _adj = slack.build_node_graph(func)
    n = len(func.nodes)
    depth = {ssa: 1 for ssa in linked}

    def lightest_cycle():
        """(weight, [edges round it]) for the lightest cycle, or None."""
        out = {v: [] for v in range(n)}
        for e in edges:
            out[e.producer].append((e.consumer, depth.get(e.value, 0), e))

        def dijkstra(src):
            dist = {src: 0}
            pred = {}
            pq = [(0, src)]
            while pq:
                c, u = heapq.heappop(pq)
                if c > dist.get(u, _INF):
                    continue
                for v, w, e in out[u]:
                    if c + w < dist.get(v, _INF):
                        dist[v], pred[v] = c + w, e
                        heapq.heappush(pq, (c + w, v))
            return dist, pred

        best = None
        for u in range(n):
            dist, pred = dijkstra(u)
            for v, w, e in out[u]:
                # A cycle: the edge u->v, then the shortest way back v -> u.
                back = dist.get(u) if v == u else None
                if v != u:
                    d2, p2 = dijkstra(v)
                    back = d2.get(u)
                    if back is None:
                        continue
                    path, at = [], u
                    while at != v:
                        pe = p2[at]
                        path.append(pe)
                        at = pe.producer
                    ring = [e] + path
                else:
                    ring = [e]
                    back = 0
                key = (w + back, sorted(str(x.value) for x in ring))
                if best is None or key < best[0]:
                    best = (key, w + back, ring)
        return None if best is None else (best[1], best[2])

    for _ in range(len(edges) + 1):
        found = lightest_cycle()
        if found is None or found[0] >= RING_MIN_STAGES:
            return depth
        weight, ring = found
        cand = [e for e in ring if e.value in depth]
        if not cand:
            # cycle_sites() runs first and links every cycle, so a cycle with
            # no linked edge at all means the two rules disagree about what a
            # cycle is -- report it rather than paper over it.
            raise EmitError(
                f"{func.name}: cycle through "
                f"{[slack.node_label(func, e.producer) for e in ring]} has no "
                f"linked edge to deepen")
        cand.sort(key=lambda e: (
            func.nodes[e.consumer].op not in HEADER_OPS, str(e.value)))
        depth[cand[0].value] += RING_MIN_STAGES - weight
    raise EmitError(f"{func.name}: ring depth did not converge")


def select_channels(func):
    """Channels whose data is read as a SELECT, not as ordinary data.

    The distinction is a timing one and it comes straight from bd_link.v's
    header: a link's `req_out` LEADS its `data_out`, by one latch arc per
    stage, and the header is explicit that this is harmless for a consumer
    that closes on ack-fall and bites only "at a boundary that SAMPLES the
    request edge".

    A select is exactly such a boundary.  bd_mux's join is
    C(x_req, ctl_req . ~s) and bd_steer's branch is req . s -- both read the
    value combinationally, gated by the request that arrived ahead of it.  Feed
    one from a DELAY(0) link and the gate evaluates for one arc on a value that
    has not landed, which shows up in simulation as an X on the branch request.

    So these channels, and only these, need their link's outgoing request
    padded.  Everywhere else DELAY stays 0, which is the cell the design review
    costed.
    """
    sel = set()
    for node in func.nodes:
        # operand 0 is the condition of a cond_br/select and the select of a
        # mux -- see result_channels(), which reads the data width off the
        # OTHER operands for exactly these three ops.
        if node.op in ("cond_br", "mux", "select") and node.operands:
            sel.add(node.operands[0])
    return sel


def link_sites(func, channels, fusion=None):
    """Which channels get a bd_link, as a set of SSA names.

    Two rules, in order, for two unrelated reasons -- measurability, then
    cycle-breaking.  Rule 2 runs second and is told what rule 1 already
    covered, so it only pays for the cycles rule 1 missed: on gcd that is 4
    extra links on top of 123.

    Swap these functions to change the storage policy.  Three alternatives
    were on the table for rule 1 and this is the cheap end of them: storage on
    every data channel (simplest, most area), storage where the uncut
    combinational depth exceeds a threshold (needs a route to decide, so it
    becomes an iterate-until-it-passes loop), or storage at basic-block
    boundaries (cheap, but nothing bounds the within-block path).

    Expect to revisit rule 1 against measurements rather than argument.  Rule
    2 is not a policy in the same sense and is not negotiable against
    measurements: below RING_MIN_STAGES storage stages per cycle the design
    does not work at all.  This function decides WHERE the links go; how deep
    each one has to be is ring_depths(), and both have to hold.  Nothing
    downstream depends on which rule put a link where -- the emitter asks these
    two functions and wires up whatever they say.

    `fusion`, when given, switches rule 1 to measurability_sites_fused() --
    BDC_CONST_FOLD's variant, storage on a fused region's external inputs
    rather than on every arithmetic op's own operands.  Rule 2 (cycle_sites)
    is unchanged either way: it operates on the full, fusion-oblivious
    handshake graph, which is safe because a fusable region can never itself
    close a cycle (that always needs a mux/control_merge), so it can never be
    asked to link an edge that fusion has already turned into a bare wire.
    Emitter.__init__ checks that this holds rather than trusting the
    argument.
    """
    if fusion is not None:
        sites = measurability_sites_fused(func, channels, fusion)
    else:
        sites = measurability_sites(func, channels)
    return sites | cycle_sites(func, sites)


# ---------------------------------------------------------------------------
# A measurement knob, OFF by default and not part of any correctness rule.
#
# On silicon each kernel costs a startlingly flat amount per loop iteration
# (xorshift 104 ns, collatz 166, collatz64 190) almost independently of what
# the loop computes, and dividing by the stages on the ring gives 15-21 ns per
# stage.  Whether that is the MARGINAL cost of a stage is a separate claim
# from the average, and the two differ if there is fixed overhead per
# iteration -- so it has to be measured as a slope, not inferred from one
# point.
#
# BDC_RING_PAD=N deepens exactly ONE link per loop: the one feeding the loop
# header, which is where ring_depths() already prefers to put depth (a header
# is the natural rest position for a loop-carried token).  Adding it in one
# place rather than spreading it keeps the sweep a clean single variable, and
# a bd_pipe at N+k circulates the same as k extra scattered stages.
#
# It changes latency and nothing else -- more storage on a ring is always
# safe, the floor is a MINIMUM.  Default 0, so the shipped build path is
# byte-identical to what it was.
RING_PAD = int(os.environ.get("BDC_RING_PAD", "0"))


def _apply_ring_pad(func, linked, depth):
    """Add RING_PAD stages to each loop's header link.  Returns what it did."""
    if RING_PAD <= 0:
        return []
    try:
        from . import slack
    except ImportError:
        import slack
    edges, adj = slack.build_node_graph(func)
    ids = list(range(len(func.nodes)))
    in_cycle = set()
    for scc in slack.tarjan_scc(ids, adj):
        if slack._is_cycle(scc, adj):
            in_cycle |= set(scc)
    padded = []
    for e in edges:
        if e.consumer not in in_cycle or e.producer not in in_cycle:
            continue
        if func.nodes[e.consumer].op not in HEADER_OPS:
            continue
        if e.value not in linked:
            continue
        depth[e.value] = depth.get(e.value, 1) + RING_PAD
        padded.append((e.value, slack.node_label(func, e.consumer), depth[e.value]))
    if not padded:
        # Say so rather than silently sweeping a variable that never moved --
        # a flat line would otherwise read as "stages are free".
        print(f"emit: BDC_RING_PAD={RING_PAD} but {func.name} has no linked "
              f"channel into a loop header; NOTHING WAS PADDED", file=sys.stderr)
    else:
        for val, who, now in padded:
            print(f"emit: BDC_RING_PAD={RING_PAD}: %{val} -> {who} now "
                  f"{now} stage(s)", file=sys.stderr)
    return padded


# ---------------------------------------------------------------------------
# The emitter

class Emitter:
    def __init__(self, func, table=None):
        self.func = func
        self.table = table or Table()
        self.ch = {}        # ssa name -> (width, is_control)
        self.lines = []
        self.delays = []    # (instance, default) in emission order
        self.units = {}     # module name -> source text, for generated cells
        self._resolve_widths()
        # BDC_CONST_FOLD's analysis: which nodes fuse into one cell, which
        # constants fold into a literal.  None when the flag is off, so every
        # site below that checks `self.fusion` takes its original branch and
        # the emitted Verilog is byte-identical to before this existed.
        self.fusion = compute_fusion(func) if BDC_CONST_FOLD else None
        # Channels with storage on them.  A linked channel has TWO net
        # bundles: the producer drives `<v>_u_*` and the link drives `<v>_*`,
        # so consumers need no idea whether a link is there.
        self.linked = link_sites(func, self.ch, fusion=self.fusion)
        if self.fusion is not None:
            # See link_sites()'s BDC_CONST_FOLD note: rule 2 cannot legally
            # ask for storage on a value fusion has already folded into a
            # cell with no channel left to put it on.  This has to hold for
            # the emitted Verilog to reference only nets that exist; check it
            # rather than trust the argument that it does.
            leaked = self.linked & self.fusion.dead_values
            if leaked:
                raise EmitError(
                    f"{func.name}: cycle-breaking wants storage on "
                    f"{sorted(leaked)}, which BDC_CONST_FOLD folded into a "
                    f"fused cell with no channel left there -- this loop "
                    f"shape is not safe to fuse this way")
        # ...and how many stages each of those links is, which is 1 everywhere
        # except on the short cycles that would otherwise sit under the floor.
        self.depth = ring_depths(func, self.linked)
        _apply_ring_pad(func, self.linked, self.depth)
        # Channels read as a SELECT rather than as ordinary data.  These are
        # the boundaries where a link's request may not outrun its own value.
        self.selects = select_channels(func)
        # Per-instance matched-delay lengths measured off a routed SDF, keyed by
        # link instance name (e.g. "ulink_n120").  Whatever is in here wins over
        # SELECT_PAD, because a number taken from the route beats a number taken
        # from an argument.  Empty by default, so an unsized build is unchanged.
        self.select_pads = load_select_pads()

    # -- widths ------------------------------------------------------------

    def _resolve_widths(self):
        """Channel widths for every value, to a fixpoint.

        A fixpoint rather than one pass because the IR is not topologically
        ordered: test_loop_free's mux0 reads %index_11 from a control_merge
        written two lines BELOW it.  That is legal MLIR and legal Verilog --
        wires have no order -- but it means a single forward sweep can ask for
        a width that does not exist yet.
        """
        for i, arg in enumerate(self.func.args):
            if arg.ssa_name:
                self.ch[arg.ssa_name] = (arg.width, arg.is_control)

        pending = list(enumerate(self.func.nodes))
        while pending:
            progress = []
            for i, node in pending:
                widths = result_channels(
                    node, [self.ch.get(o) for o in node.operands])
                if len(widths) != len(node.results):
                    raise EmitError(
                        f"{node.op} at line {node.src_line}: width rule gave "
                        f"{len(widths)} result type(s) for {len(node.results)} "
                        f"result(s)")
                if any(w is None for w in widths):
                    progress.append((i, node))
                    continue
                for name, w in zip(node.results, widths):
                    self.ch[name] = w
            if len(progress) == len(pending):
                stuck = sorted({n.op for _, n in progress})
                unknown = sorted({o for _, n in progress for o in n.operands
                                  if o not in self.ch})
                raise EmitError(
                    f"could not resolve channel widths; {len(progress)} op(s) "
                    f"left, kinds {stuck}. Unresolved operands: "
                    f"{unknown[:8]}{' ...' if len(unknown) > 8 else ''}. Either "
                    f"an operand has no producer, which materialize should have "
                    f"made impossible, or every op in a cycle is asking a rule "
                    f"that needs a width from inside that same cycle")
            pending = progress

    def width(self, ssa):
        return self.ch[ssa][0]

    def is_control(self, ssa):
        return self.ch[ssa][1]

    # -- net helpers -------------------------------------------------------

    def req(self, ssa):
        return f"{vname(ssa)}_req"

    def ack(self, ssa):
        return f"{vname(ssa)}_ack"

    def data(self, ssa):
        """The data net, or a literal zero for a control channel.

        Control channels genuinely have no data net; handing back 1'b0 is what
        lets a cell that needs a W parameter be wired up without one existing.
        Reading this on an OUTPUT port would be a bug, so emitters must use
        `data_out` for that direction instead.
        """
        return "1'b0" if self.is_control(ssa) else f"{vname(ssa)}_data"

    def data_out(self, ssa):
        """The data net for an output port: unconnected on a control channel.

        The bd-config convention requires the output be genuinely unread --
        connecting it anywhere puts the datapath LUTs back that leaving it
        dangling removes.
        """
        return "" if self.is_control(ssa) else f"{vname(ssa)}_data"

    # Producer-side accessors.  Identical to the consumer-side ones unless the
    # channel has a bd_link on it, in which case the producer drives the link's
    # input and the link drives everything the consumer sees.  Keeping this as
    # a separate set of accessors -- rather than a flag threaded through each
    # lowering -- is what lets the storage policy change without touching a
    # single op's code.
    def _u(self, ssa):
        return f"{vname(ssa)}_u" if ssa in self.linked else vname(ssa)

    def oreq(self, ssa):
        return f"{self._u(ssa)}_req"

    def oack(self, ssa):
        return f"{self._u(ssa)}_ack"

    def odata(self, ssa):
        return "1'b0" if self.is_control(ssa) else f"{self._u(ssa)}_data"

    def odata_out(self, ssa):
        return "" if self.is_control(ssa) else f"{self._u(ssa)}_data"

    def emit_links(self):
        """One link per linked channel, between producer and consumer.

        A bd_pipe rather than a bd_link wherever ring_depths() asked for more
        than one stage -- the two have the same port list, and bd_pipe at N=1
        is a bd_link, so the split here is only so that the common case reads
        as the cell it is.

        A link on a CONTROL channel is a link on the handshake alone.  Rule 2
        in link_sites() puts them there, and a control channel has no data net
        declared at either end -- so the link's data_out must be left
        genuinely unconnected, exactly as data_out() does for every other
        cell.  Naming a net that was never declared would not error: Verilog
        would invent a one-bit wire and the link would look connected.
        """
        for ssa in sorted(self.linked):
            w = self.width(ssa)
            inst = f"ulink_{vname(ssa)}"
            n = self.depth.get(ssa, 1)
            # DELAY 0 everywhere except in front of a select, where the link's
            # request would otherwise arrive a latch arc ahead of the value the
            # select is made of.  One delay element per stage matches the lead
            # bd_link.v measures (one latch arc per stage); like every other
            # matched delay here it is a placeholder that tighten.py replaces
            # with the post-route number.
            # Four elements per stage, not one.  The lead to cover is a
            # latch arc (152 ps in the sim model, and bd_link.v measures the
            # same on silicon) while a bd_delay element is a LUT1 whose RISE
            # arc is 56 ps -- so it takes three to cover one latch arc, and a
            # fourth is the guardband the bundling constraint asks for.
            # SELECT_PAD, not a literal 4.  The 4 above was derived from the
            # INTRINSIC lead only -- a latch arc over a LUT1 rise arc -- and it
            # ignores the routing skew between the request net and the select
            # net, which on this part is most of every hop.  On silicon that
            # shows up as vectors whose loop has to take a real branch simply
            # never completing, deterministic per bitstream and DIFFERENT on a
            # different place-and-route seed, with err_sticky always clean
            # because a mis-steered token deadlocks rather than computing a
            # wrong answer.  Until tighten.py audits select channels and hands
            # back a per-route number, this is the knob that buys margin.
            #
            # A GLOBAL CONSTANT CANNOT WORK HERE, and that is measured, not
            # argued.  Swept on silicon against the sixteen-vector gcd rig:
            #
            #     pad  4   7 of 16 vectors complete      6820 LUT sites
            #     pad 32  16 of 16 on one route,          7492
            #             9 of 16 after an unrelated
            #             one-LUT change to the rig       7483
            #     pad 64   8 of 16, and gcd(1,1) -- the
            #             most trivial vector there is
            #             -- was one of the dead ones     8251
            #
            # Not monotone.  Padding a select buys margin on THAT channel and
            # spends it everywhere else: 24 channels of 64 elements is 1536
            # LUT1s of chain, congestion rises, and the routing skew on the
            # selects that were already marginal grows faster than the padded
            # ones improve.  The number has to come from the route, per channel.
            pad = SELECT_PAD * n if ssa in self.selects else 0
            pad = self.select_pads.get(inst, pad)
            d = self.delay(inst, pad)
            if n > 1:
                self.emit(f"    bd_pipe #(.W({max(w, 1)}), .N({n}), "
                          f".DELAY({d})) {inst} (")
            else:
                self.emit(f"    bd_link #(.W({max(w, 1)}), .DELAY({d})) {inst} (")
            self.emit(f"        .rst(rst),")
            self.emit(f"        .req_in({self.oreq(ssa)}), .ack_in({self.oack(ssa)}), "
                      f".data_in({self.odata(ssa)}),")
            v = vname(ssa)
            self.emit(f"        .req_out({v}_req), .ack_out({v}_ack), "
                      f".data_out({self.data_out(ssa)}));")

    def emit(self, text=""):
        self.lines.append(text)

    def delay(self, inst, default):
        self.delays.append((inst, default))
        return f"DELAY_{inst.upper()}"

    # -- per-op lowering ---------------------------------------------------

    def lower(self, node, index):
        try:
            self.table.lookup(node)
        except Unmapped as e:
            raise EmitError(f"line {node.src_line}: {e}") from None

        fn = getattr(self, f"_op_{node.op}", None)
        if fn is None:
            raise EmitError(
                f"line {node.src_line}: handshake op {node.op!r} is in "
                f"bd-config.json but has no lowering in emit.py. Write one; "
                f"do not fall through to something adjacent")
        inst = instname(node, index)
        self.emit(f"    // {node.op}  (line {node.src_line})")
        fn(node, inst)
        self.emit()

    def _pass_through(self, src, dst):
        """One channel driving another: a rename, not a cell."""
        self.emit(f"    assign {self.oreq(dst)} = {self.req(src)};")
        self.emit(f"    assign {self.ack(src)} = {self.oack(dst)};")
        if not self.is_control(dst):
            self.emit(f"    assign {self.odata(dst)} = {self.data(src)};")

    def _op_br(self, node, inst):
        self._pass_through(node.operands[0], node.results[0])

    def _reshape(self, node, expr):
        """trunci / extui / extsi: the handshake passes straight through and
        only the data bundle changes shape.

        None of the three has any logic depth -- a slice is a wire and a
        zero-extend is a constant -- so none gets a matched delay.  That is the
        whole reason bdc/compute.py's header refuses to build units for them:
        a unit would place a bd_join and a bd_delay around a renaming.

        The request is NOT delayed here even though the data changes, because
        it does not change in a way that costs time.  If that ever stops being
        true -- if a reshape grows a mux -- it stops being a reshape and needs
        a unit, and this method is the wrong place to notice that.
        """
        src, dst = node.operands[0], node.results[0]
        self.emit(f"    assign {self.oreq(dst)} = {self.req(src)};")
        self.emit(f"    assign {self.ack(src)} = {self.oack(dst)};")
        self.emit(f"    assign {self.odata(dst)} = {expr};")

    def _op_trunci(self, node, inst):
        w = self.width(node.results[0])
        self._reshape(node, f"{self.data(node.operands[0])}[{max(w, 1) - 1}:0]")

    def _op_extui(self, node, inst):
        src, dst = node.operands[0], node.results[0]
        sw, dw = max(self.width(src), 1), max(self.width(dst), 1)
        if dw <= sw:
            raise EmitError(f"line {node.src_line}: extui from {sw} to {dw} "
                            f"bits does not widen. Dynamatic emitted an "
                            f"extension that is not one; do not silently slice")
        self._reshape(node, f"{{{dw - sw}'b0, {self.data(src)}}}")

    def _op_extsi(self, node, inst):
        src, dst = node.operands[0], node.results[0]
        sw, dw = max(self.width(src), 1), max(self.width(dst), 1)
        if dw <= sw:
            raise EmitError(f"line {node.src_line}: extsi from {sw} to {dw} "
                            f"bits does not widen. Dynamatic emitted an "
                            f"extension that is not one; do not silently slice")
        d = self.data(src)
        self._reshape(node, f"{{{{{dw - sw}{{{d}[{sw - 1}]}}}}, {d}}}")

    def _op_merge(self, node, inst):
        ops = node.operands
        if len(ops) == 1:
            self._pass_through(ops[0], node.results[0])
            return
        z = node.results[0]
        w = self.width(z)
        n = len(ops)
        self.units.setdefault(f"bdc_amerge{n}_{w}", emit_amerge(w, n))
        d = self.delay(inst, compute.merge_delay(n))
        self.emit(f"    bdc_amerge{n}_{w} #(.DELAY({d})) {inst} (")
        self.emit(f"        .rst(rst),")
        for k, o in enumerate(ops):
            self.emit(f"        .in{k}_req({self.req(o)}), "
                      f".in{k}_ack({self.ack(o)}), .in{k}_data({self.data(o)}),")
        self.emit(f"        .z_req({self.oreq(z)}), .z_ack({self.oack(z)}), "
                  f".z_data({self.odata_out(z)}), .index());")

    def _op_control_merge(self, node, inst):
        """result + index.  Two channels out of one arrival, so even the
        single-input case needs a fork: the index is a real channel with its
        own consumer, not a side effect of the result."""
        ops = node.operands
        res, idx = node.results
        if len(ops) == 1:
            self.emit(f"    bd_fork #(.N(2)) {inst} (")
            self.emit(f"        .rst(rst), .req({self.req(ops[0])}), "
                      f".ack({self.ack(ops[0])}),")
            self.emit(f"        .req_out({{{self.oreq(idx)}, {self.oreq(res)}}}),")
            self.emit(f"        .ack_in({{{self.oack(idx)}, {self.oack(res)}}}));")
            if not self.is_control(res):
                self.emit(f"    assign {self.odata(res)} = {self.data(ops[0])};")
            # One predecessor means the index is a compile-time constant, and
            # a constant needs no matched delay: it is valid before the
            # circuit powers on, never mind before the request arrives.
            self.emit(f"    assign {self.odata(idx)} = "
                      f"{self.width(idx)}'d0;")
            return
        # The arbitrated merge already produces the index, so result and index
        # leave together and both need forking off one arrival.  The merge's
        # own matched delay covers the index.
        w = self.width(res)
        n = len(ops)
        iw = max(1, (n - 1).bit_length())
        if self.width(idx) < iw:
            raise EmitError(
                f"control_merge at line {node.src_line}: {n} inputs need "
                f"{iw} index bit(s) but the index channel is "
                f"{self.width(idx)} wide. Do not truncate a winner")
        self.units.setdefault(f"bdc_amerge{n}_{w}", emit_amerge(w, n))
        d = self.delay(inst, compute.merge_delay(n))
        m_req, m_ack = f"{inst}_req", f"{inst}_ack"
        self.emit(f"    wire {m_req}, {m_ack};")
        if not self.is_control(res):
            self.emit(f"    wire [{max(w, 1) - 1}:0] {inst}_data;")
        self.emit(f"    bdc_amerge{n}_{w} #(.DELAY({d})) {inst} (")
        self.emit(f"        .rst(rst),")
        for k, o in enumerate(ops):
            self.emit(f"        .in{k}_req({self.req(o)}), "
                      f".in{k}_ack({self.ack(o)}), .in{k}_data({self.data(o)}),")
        self.emit(f"        .z_req({m_req}), .z_ack({m_ack}), "
                  f".z_data({inst + '_data' if w else ''}), "
                  f".index({self.odata(idx)}[{iw - 1}:0]));")
        if self.width(idx) > iw:
            self.emit(f"    assign {self.odata(idx)}"
                      f"[{self.width(idx) - 1}:{iw}] = "
                      f"{self.width(idx) - iw}'d0;")
        self.emit(f"    bd_fork #(.N(2)) {inst}_f (")
        self.emit(f"        .rst(rst), .req({m_req}), .ack({m_ack}),")
        self.emit(f"        .req_out({{{self.oreq(idx)}, {self.oreq(res)}}}),")
        self.emit(f"        .ack_in({{{self.oack(idx)}, {self.oack(res)}}}));")
        if not self.is_control(res):
            self.emit(f"    assign {self.odata(res)} = {inst}_data;")

    def _op_fork(self, node, inst):
        x = node.operands[0]
        n = len(node.results)
        reqs = ", ".join(self.oreq(r) for r in reversed(node.results))
        acks = ", ".join(self.oack(r) for r in reversed(node.results))
        self.emit(f"    bd_fork #(.N({n})) {inst} (")
        self.emit(f"        .rst(rst), .req({self.req(x)}), .ack({self.ack(x)}),")
        self.emit(f"        .req_out({{{reqs}}}), .ack_in({{{acks}}}));")
        # Data is broadcast, which is wiring -- bd_fork routes the handshake
        # and nothing else.
        for r in node.results:
            if not self.is_control(r):
                self.emit(f"    assign {self.odata(r)} = {self.data(x)};")

    _op_lazy_fork = _op_fork

    def _op_join(self, node, inst):
        ops = node.operands
        z = node.results[0]
        reqs = ", ".join(self.req(o) for o in reversed(ops))
        acks = ", ".join(self.ack(o) for o in reversed(ops))
        self.emit(f"    bd_join #(.N({len(ops)})) {inst} (")
        self.emit(f"        .rst(rst), .req_in({{{reqs}}}), .ack_out({{{acks}}}),")
        self.emit(f"        .req({self.oreq(z)}), .ack({self.oack(z)}));")

    def _op_cond_br(self, node, inst):
        """The condition is its own channel, so it has to be joined with the
        data before the steer sees it -- bd_steer takes a request and a LEVEL,
        not two channels.  Joining is also what makes the level legal: the
        bundling contract holds s still from req-rise to ack-fall, and after a
        join the request only rises once the condition token has arrived."""
        cond, dat = node.operands
        true_r, false_r = node.results
        jr, ja = f"{inst}_req", f"{inst}_ack"
        self.emit(f"    wire {jr}, {ja};")
        self.emit(f"    bd_join #(.N(2)) {inst}_j (")
        self.emit(f"        .rst(rst), .req_in({{{self.req(cond)}, {self.req(dat)}}}),")
        self.emit(f"        .ack_out({{{self.ack(cond)}, {self.ack(dat)}}}),")
        self.emit(f"        .req({jr}), .ack({ja}));")
        # req0 = req.~s, req1 = req.s -- so branch 1 is the true result.
        self.emit(f"    bd_steer {inst} (")
        self.emit(f"        .req({jr}), .s({self.data(cond)}[0]), .ack({ja}),")
        self.emit(f"        .req0({self.oreq(false_r)}), .ack0({self.oack(false_r)}),")
        self.emit(f"        .req1({self.oreq(true_r)}), .ack1({self.oack(true_r)}));")
        for r in (true_r, false_r):
            if not self.is_control(r):
                self.emit(f"    assign {self.odata(r)} = {self.data(dat)};")

    def _op_mux(self, node, inst):
        sel = node.operands[0]
        ins = node.operands[1:]
        z = node.results[0]
        w = self.width(z)
        n = len(ins)
        d = self.delay(inst, compute.CELL_DELAY["wide"])
        if n == 2:
            # s = 0 picks x, so x is input 0 -- the order the index counts in.
            self.emit(f"    bd_mux #(.W({max(w, 1)}), .DELAY({d})) {inst} (")
            self.emit(f"        .rst(rst),")
            self.emit(f"        .x_req({self.req(ins[0])}), "
                      f".x_ack({self.ack(ins[0])}), .x_data({self.data(ins[0])}),")
            self.emit(f"        .y_req({self.req(ins[1])}), "
                      f".y_ack({self.ack(ins[1])}), .y_data({self.data(ins[1])}),")
            self.emit(f"        .ctl_req({self.req(sel)}), "
                      f".ctl_ack({self.ack(sel)}), .s({self.data(sel)}[0]),")
            self.emit(f"        .z_req({self.oreq(z)}), .z_ack({self.oack(z)}), "
                      f".z_data({self.odata_out(z)}));")
            return
        iw = max(1, (n - 1).bit_length())
        if self.width(sel) < iw:
            raise EmitError(
                f"mux at line {node.src_line}: {n} inputs need {iw} index "
                f"bit(s) but the index channel is {self.width(sel)} wide")
        self.units.setdefault(f"bdc_muxn{n}_{w}", emit_muxn(w, n))
        self.emit(f"    bdc_muxn{n}_{w} #(.DELAY({d})) {inst} (")
        self.emit(f"        .rst(rst),")
        for k, o in enumerate(ins):
            self.emit(f"        .in{k}_req({self.req(o)}), "
                      f".in{k}_ack({self.ack(o)}), .in{k}_data({self.data(o)}),")
        self.emit(f"        .ctl_req({self.req(sel)}), "
                  f".ctl_ack({self.ack(sel)}), "
                  f".s({self.data(sel)}[{iw - 1}:0]),")
        self.emit(f"        .z_req({self.oreq(z)}), .z_ack({self.oack(z)}), "
                  f".z_data({self.odata_out(z)}));")

    def _op_source(self, node, inst):
        z = node.results[0]
        w = max(self.width(z), 1)
        self.emit(f"    bd_src #(.W({w}), .VAL({w}'d0)) {inst} (")
        self.emit(f"        .req({self.oreq(z)}), .ack({self.oack(z)}), "
                  f".data({self.odata_out(z)}));")

    def _op_sink(self, node, inst):
        x = node.operands[0]
        w = max(self.width(x), 1)
        self.emit(f"    bd_snk #(.W({w})) {inst} (")
        self.emit(f"        .req({self.req(x)}), .ack({self.ack(x)}), "
                  f".data({self.data(x)}));")

    def _op_constant(self, node, inst):
        ctl = node.operands[0]
        z = node.results[0]
        value = node.attrs.get("value")
        raw = getattr(value, "value", value)
        if not isinstance(raw, int):
            raise EmitError(f"constant at line {node.src_line} has value "
                            f"{value!r}, which is not an integer")
        w = self.width(z)
        # Two's complement into an unsigned literal: a negative constant is a
        # bit pattern here, and Verilog would sign-extend a bare minus into the
        # width instead of masking to it.
        self.emit(f"    assign {self.odata(z)} = {w}'h{raw & ((1 << w) - 1):x};")
        self.emit(f"    assign {self.oreq(z)} = {self.req(ctl)};")
        self.emit(f"    assign {self.ack(ctl)} = {self.oack(z)};")

    def _op_end(self, node, inst):
        """The function's results, which are ports, not cells."""
        if len(node.operands) != len(self.func.results):
            raise EmitError(
                f"end at line {node.src_line} has {len(node.operands)} "
                f"operand(s) for {len(self.func.results)} function result(s)")
        for res, src in zip(self.func.results, node.operands):
            base = portname(res.name)
            self.emit(f"    assign {base}_req = {self.req(src)};")
            self.emit(f"    assign {self.ack(src)} = {base}_ack;")
            if not self.is_control(src):
                self.emit(f"    assign {base}_data = {self.data(src)};")

    # -- compute units -----------------------------------------------------

    def _compute(self, node, inst, chans):
        """Any op whose lowering is a bdc/compute.py unit.

        `chans` maps the unit's port prefixes onto operand positions.  The
        order is not guessable and is not the operand order for `select`:
        handshake spells it select(cond, true, false) and the unit computes
        `s ? a : b`, so cond is `s` and the true value is `a`.
        """
        pred = None
        if node.op == "cmpi":
            pred = self._predicate(node)
        w = self.width(node.operands[chans["a"]])
        name = compute.unit_name(node.op, w, pred)
        self.units.setdefault(name, compute.emit_unit(node.op, w, pred))
        d = self.delay(inst, compute.default_delay(node.op, w))
        z = node.results[0]
        self.emit(f"    {name} #(.DELAY({d})) {inst} (")
        self.emit(f"        .rst(rst),")
        for port, pos in sorted(chans.items()):
            o = node.operands[pos]
            self.emit(f"        .{port}_req({self.req(o)}), "
                      f".{port}_ack({self.ack(o)}), "
                      f".{port}_data({self.data(o)}),")
        self.emit(f"        .z_req({self.oreq(z)}), .z_ack({self.oack(z)}), "
                  f".z_data({self.odata_out(z)}));")

    @staticmethod
    def _predicate(node):
        for item in node.arg_items:
            if isinstance(item, parse.OperandSegment):
                for sub in item.items:
                    if isinstance(sub, parse.LiteralArg) and sub.text in compute.CMPI:
                        return sub.text
        raise EmitError(f"cmpi at line {node.src_line} carries no recognised "
                        f"predicate; known ones are {sorted(compute.CMPI)}")

    # -- BDC_CONST_FOLD: fused regions --------------------------------------

    def lower_fused(self, region, index):
        """One handshake op AS the anchor of a fused region.

        Every other member of `region` was put in self.fusion.skip by
        compute_fusion() and emit_func's driver loop never calls lower() on
        them -- the whole region becomes this one instantiation.  Mirrors
        _compute() above except for reading the wiring off `region` instead
        of a single node's operands.
        """
        nodes = self.func.nodes
        anchor = nodes[region.anchor]
        try:
            self.table.lookup(anchor)
        except Unmapped as ex:
            raise EmitError(f"line {anchor.src_line}: {ex}") from None
        inst = instname(anchor, index)
        chain = " + ".join(nodes[i].op for i in region.node_ids)
        self.emit(f"    // {chain}  fused by BDC_CONST_FOLD "
                  f"(anchor line {anchor.src_line})")
        name, default = self._emit_fused_module(region, inst)
        d = self.delay(inst, default)
        z = anchor.results[0]
        self.emit(f"    {name} #(.DELAY({d})) {inst} (")
        self.emit(f"        .rst(rst),")
        for k, ssa in enumerate(region.ext_inputs):
            p = f"e{k}"
            self.emit(f"        .{p}_req({self.req(ssa)}), "
                      f".{p}_ack({self.ack(ssa)}), .{p}_data({self.data(ssa)}),")
        self.emit(f"        .z_req({self.oreq(z)}), .z_ack({self.oack(z)}), "
                  f".z_data({self.odata_out(z)}));")
        self.emit()

    def _emit_fused_module(self, region, inst):
        """The fused region as a self-contained Verilog module: one
        keep_hierarchy boundary, one bd_join over region.ext_inputs, one
        matched delay, and the interior ops written as plain wire assigns so
        yosys can fold constants and share logic across the whole region.

        The module name is keyed on `inst`, the anchor's own instance name,
        which instname() already guarantees unique per function -- unlike
        compute.py's single-op cells, two fused regions are only the same
        netlist by coincidence (their folded constants may differ), so this
        deliberately does not try to share modules across instances the way
        compute.emit_unit's (op, width) naming does.
        """
        nodes = self.func.nodes
        name = f"bdc_fused_{inst}"

        default_total = 0
        body_lines = []
        node_wire = {}
        for i in region.node_ids:
            n = nodes[i]
            w = self.width(n.operands[_FUSABLE_CHANS[n.op]["a"]])
            default_total += compute.default_delay(n.op, w)
            pred = self._predicate(n) if n.op == "cmpi" else None

            def ref_expr(port, _i=i, _w=w):
                kind, val = region.ref[(_i, port)]
                if kind == "const":
                    pw = 1 if port == "s" else _w
                    return f"{pw}'h{val & ((1 << pw) - 1):x}"
                if kind == "ext":
                    return f"e{val}_data"
                return node_wire[val]

            ports = {p: ref_expr(p) for p in _FUSABLE_CHANS[n.op]}
            extra, expr, out_w = _fused_node_expr(n.op, w, pred, ports, f"n{i}")
            wname = f"w_n{i}"
            body_lines.extend(extra)
            if n.op == "cmpi":
                body_lines.append(f"    wire cmp_z_n{i} = {expr};")
                body_lines.append(f"    wire {wname};")
                body_lines.append(
                    f"    (* keep *) LUT1 #(.INIT(2'h2)) uz_n{i} "
                    f"(.I0(cmp_z_n{i}), .O({wname}));")
            else:
                body_lines.append(f"    wire [{out_w - 1}:0] {wname} = {expr};")
            node_wire[i] = wname

        anchor = nodes[region.anchor]
        out_w = 1 if anchor.op == "cmpi" else self.width(
            anchor.operands[_FUSABLE_CHANS[anchor.op]["a"]])

        ext_w = [self.width(ssa) for ssa in region.ext_inputs]
        decls = []
        for k, pw in enumerate(ext_w):
            pad = ' ' * max(0, 7 - len(str(pw - 1)))
            decls += [f"     input  wire             e{k}_req,",
                      f"     output wire             e{k}_ack,",
                      f"     input  wire [{pw - 1}:0]{pad}e{k}_data,"]
        req_cat = "{" + ", ".join(f"e{k}_req"
                                  for k in reversed(range(len(ext_w)))) + "}"
        ack_cat = "{" + ", ".join(f"e{k}_ack"
                                  for k in reversed(range(len(ext_w)))) + "}"

        chain = " -> ".join(nodes[i].op for i in region.node_ids)
        text = f"""
// Fused region: {chain}.  Generated by bdc/emit.py under BDC_CONST_FOLD --
// do not edit.  One keep_hierarchy boundary, one bd_join, one matched delay
// for the whole region: see the BDC_CONST_FOLD block comment above
// FUSABLE_OPS in bdc/emit.py for why this does not cost auditability.
`default_nettype none
(* keep_hierarchy *)
module {name} #(parameter DELAY = {default_total})
    (input  wire             rst,
{chr(10).join(decls)}
     output wire             z_req,
     input  wire             z_ack,
     output wire [{out_w - 1}:0]{' ' * max(0, 7 - len(str(out_w - 1)))}z_data);

    // Every external operand must have arrived before the region's logic
    // means anything.  A folded constant is not among these -- see
    // compute_fusion(): it is always available and never returns to zero,
    // so joining against it would be a rendezvous with something that
    // cannot be late.
    wire joined;
    bd_join #(.N({len(ext_w)})) ujoin (
        .rst(rst), .req_in({req_cat}), .ack_out({ack_cat}),
        .req(joined), .ack(z_ack));

    wire either;
    (* keep *) LUT1 #(.INIT(2'h2)) uor (.I0(joined), .O(either));
    bd_delay #(.N(DELAY)) udly (.a(either), .z(z_req));

    // The datapath.  yosys picks the implementation, across the WHOLE
    // region at once; the matched delay above is what makes whatever it
    // picks safe.
{chr(10).join(body_lines)}
    assign z_data = {node_wire[region.anchor]};
endmodule
`default_nettype wire
"""
        self.units.setdefault(name, text)
        return name, default_total


def _bind_compute(op):
    chans = {"a": 0, "b": 1}
    if op == "select":
        chans = {"s": 0, "a": 1, "b": 2}

    def fn(self, node, inst, _chans=chans):
        self._compute(node, inst, _chans)
    return fn


for _op in ("addi", "subi", "muli", "cmpi", "andi", "ori", "xori",
            "shli", "shrsi", "shrui", "select"):
    setattr(Emitter, f"_op_{_op}", _bind_compute(_op))


# ---------------------------------------------------------------------------
# Module assembly

def emit_func(func, table=None):
    """One handshake.func as (module_text, generated_units, delay_list)."""
    if func.is_declaration:
        raise EmitError(f"@{func.name} has no body")

    e = Emitter(func, table)

    seen = {}
    for ssa in e.ch:
        v = vname(ssa)
        if v in seen:
            raise EmitError(f"SSA names {seen[v]!r} and {ssa!r} both sanitise "
                            f"to {v!r}; the net name mapping is not injective")
        seen[v] = ssa

    for i, node in enumerate(func.nodes):
        if e.fusion is not None and i in e.fusion.skip:
            # Absorbed (source, constant) pair, or a fused region member
            # other than its anchor -- not individually lowered, but still
            # validated against bd-config.json exactly as lower() would.
            try:
                e.table.lookup(node)
            except Unmapped as ex:
                raise EmitError(f"line {node.src_line}: {ex}") from None
            continue
        if e.fusion is not None and i in e.fusion.anchor_region:
            e.lower_fused(e.fusion.anchor_region[i], i)
            continue
        e.lower(node, i)

    if e.linked:
        e.emit("    // Storage.  See link_sites() for the policy and for what")
        e.emit("    // went wrong without it.")
        e.emit_links()

    # Ports.  Arguments are driven from outside, results drive outward.
    ports = ["    input  wire             rst"]
    for arg in func.args:
        b = portname(arg.name)
        ports.append(f"    input  wire             {b}_req")
        ports.append(f"    output wire             {b}_ack")
        if not arg.is_control:
            ports.append(f"    input  wire [{arg.width - 1}:0]     {b}_data")
    for res in func.results:
        b = portname(res.name)
        ports.append(f"    output wire             {b}_req")
        ports.append(f"    input  wire             {b}_ack")
        if not res.is_control:
            ports.append(f"    output wire [{res.width - 1}:0]     {b}_data")

    # ---- probe ports -------------------------------------------------------
    # BDC_PROBE=<chan>[,<chan>...] brings an INTERNAL channel out of the kernel
    # so it can be latched and read back over JTAG.
    #
    # This exists because a gate-level simulation of the routed netlist is a
    # MODEL, and on gcd the model and the die disagreed in a way neither could
    # settle alone: cells/gls said `cmpi sgt(diff, -1)` returns 0 for positive
    # diff, the board failed exactly the vectors that predicts, and the change
    # that provably removed the modelled cause left the board's verdict word
    # bit-for-bit unchanged.  One of the two is lying and only the silicon
    # knows which.  A probe port is how you ask it.
    #
    # The probe is a TAP, never a consumer: it reads <chan>_data and <chan>_req
    # and drives no ack, so it cannot complete a handshake, cannot steal a
    # token, and cannot change the schedule of the design it is measuring.  It
    # does add fanout, which moves placement -- so a probe build is a different
    # route and its verdict word is only comparable to another probe build.
    # A `_u` suffix asks for the PRODUCER side of a linked channel, in front of
    # its link, and that distinction is the whole reason two probes can be
    # compared at all.  Between a cell's data input and its own data output
    # there is no storage, so the two are the same iteration by construction and
    # a check across them needs no skew argument.  Across a LINK they are not:
    # the link holds a result while the input channel is free to accept the next
    # value, so `n135__2` and `n136` caught at one instant may be a trip apart.
    probes = []
    for name in [p for p in PROBE if p]:
        base, pre = (name[:-2], True) if name.endswith("_u") else (name, False)
        ssa = next((s for s in e.ch if vname(s) == base), None)
        if ssa is None:
            raise EmitError(
                f"--probe names {name!r}, which is not a channel in @{func.name}. "
                f"Channels are named as they are in the emitted Verilog "
                f"(`n136`, not `%136`); `grep 'wire n.*_req' <output>` lists them. "
                f"A trailing `_u` asks for the pre-link bundle and is only valid "
                f"on a channel that carries a link.")
        if pre and ssa not in e.linked:
            raise EmitError(
                f"--probe names {name!r}, but channel {base!r} carries no link, "
                f"so there is no pre-link bundle to tap -- probe {base!r}.")
        if e.fusion is not None and ssa in e.fusion.dead_values:
            raise EmitError(
                f"--probe names {name!r}, but BDC_CONST_FOLD folded that "
                f"channel into a fused cell -- there is no net left to tap. "
                f"Probe an external input or the region's own output instead.")
        w, ctl = e.ch[ssa]
        probes.append((name, w, ctl))

    for name, w, ctl in probes:
        ports.append(f"    output wire             probe_{name}_req")
        if not ctl:
            ports.append(f"    output wire [{w - 1}:0]     probe_{name}_data")

    # The bare name taps the CONSUMER side of any link on the channel -- the
    # same nets the real consumer sees, so what is measured is the value the
    # design acts on rather than one a link is still holding.  `<name>_u` taps
    # the producer side instead; see above for when that is the one you want.
    probe_taps = "\n".join(
        [f"    // Probe taps.  Read-only: no ack is driven from these."] +
        [line for name, w, ctl in probes
         for line in ([f"    assign probe_{name}_req = {name}_req;"] +
                      ([] if ctl else
                       [f"    assign probe_{name}_data = {name}_data;"]))]
    ) if probes else ""

    params = ", ".join(f"parameter DELAY_{i.upper()} = {d}"
                       for i, d in e.delays)
    param_clause = f" #({params})" if params else ""

    # Every channel is declared, function arguments included, and every driver
    # is an assign.  Declaring an argument's channel implicitly as
    # `wire v_req = b_req` was shorter and stopped working the moment an
    # argument could carry a link -- the link needs to drive a wire that
    # already exists.  Uniform is worth more than short here.
    decls = []
    for ssa, (w, ctl) in e.ch.items():
        if e.fusion is not None and ssa in e.fusion.dead_values:
            # Absorbed by BDC_CONST_FOLD: an eliminated (source, constant)
            # pair, or a fused region member other than its anchor.  Nothing
            # drives or reads these nets any more, so they are not declared
            # at all rather than left as unused wires -- the "DECLARATIONS
            # FIRST" note below is about ordering what IS referenced, and a
            # declaration for a name nothing references invites exactly the
            # confusion that note is guarding against.
            continue
        decls.append(f"    wire {vname(ssa)}_req, {vname(ssa)}_ack;")
        if not ctl:
            decls.append(f"    wire [{w - 1}:0] {vname(ssa)}_data;")
        if ssa in e.linked:
            # A linked channel has a second bundle, in front of its link.
            u = f"{vname(ssa)}_u"
            decls.append(f"    wire {u}_req, {u}_ack;")
            if not ctl:
                decls.append(f"    wire [{w - 1}:0] {u}_data;")

    # A function argument's channel IS the port. Bridged onto the PRODUCER
    # side, because an argument's channel can carry a link like any other.
    bridge = []
    for arg in func.args:
        if not arg.ssa_name:
            continue
        b, v = portname(arg.name), e._u(arg.ssa_name)
        bridge.append(f"    assign {v}_req = {b}_req;")
        bridge.append(f"    assign {b}_ack = {v}_ack;")
        if not arg.is_control:
            bridge.append(f"    assign {v}_data = {b}_data;")

    body = "\n".join(
        [f"(* keep_hierarchy *)",
         f"module bdc_{func.name}{param_clause} (",
         ",\n".join(ports) + ");",
         "",
         "    // Every internal channel: req and ack always, data unless the",
         "    // channel is control -- a control channel has no data net at",
         "    // all, which is what makes the W=1-tied-low convention free.",
         "\n".join(decls),
         "",
         # DECLARATIONS FIRST, AND THAT ORDER IS LOAD-BEARING.
         #
         # These assigns used to come before the wires they drive.  Verilog
         # wires have no order, so yosys read it exactly as intended and every
         # synthesis gate passed -- flow.sh routed a design with real 32-bit
         # carry chains in it.  iverilog does not: an undeclared name in an
         # assign becomes an IMPLICIT ONE-BIT NET, so `n_arg0_data` was 1 bit
         # wide in simulation and every argument was truncated to its low bit.
         #
         # It was reported only as `warning: implicit definition of wire`,
         # buried in a wall of them, and it silently made the simulation
         # gate's answers meaningless while every other gate stayed green.
         # Do not move these back above `decls`.
         "    // Function arguments, as channels.",
         "\n".join(bridge),
         "",
         "\n".join(e.lines),
         probe_taps,
         "endmodule"])
    return body, e.units, e.delays


def emit_top(func, delays, inst="uut"):
    """A two-pin top, in the shape of cells/verify/soak_top.v.

    Not a functioning kernel and not trying to be -- like soak_top.v it exists
    so that nothing folds, nothing merges, and every net is real enough for the
    router.  The gates downstream measure topology and arrival times.

    The two rules it exists to obey are bdc/compute.py's, learned the hard way
    and restated here because they bite a whole kernel exactly as they bit one
    unit: operands must come from real STATE, or every bit is a function of one
    pin and yosys folds the datapath away; and the environment must not close a
    COMBINATIONAL loop around the design, or tighten.py sees every matched
    delay as a state node and measures requests arriving at themselves.
    """
    name = f"bdc_{func.name}"
    inputs = [portname(a.name) for a in func.args]
    outputs = [portname(r.name) for r in func.results]
    total = sum(a.width for a in func.args)
    # Every driven pin gets its OWN spine bit and they must not overlap.  The
    # first version let the result acknowledges land on top of the last
    # argument's data slice, which does not fail: it routes, and it silently
    # ties an acknowledge to a data bit of the design under test.
    req_base, data_base = 0, len(inputs)
    ack_base = data_base + total
    nb = max(32, ack_base + len(outputs))
    seed = int("5A3C" * (nb // 16 + 1), 16) & ((1 << (nb - 1)) - 1)

    defines = "\n".join(
        f"`ifndef BD_SZ_{inst.upper()}_{i.upper()}\n"
        f" `define BD_SZ_{inst.upper()}_{i.upper()} {d}\n"
        f"`endif" for i, d in delays)
    params = ",\n".join(f"        .DELAY_{i.upper()}(`BD_SZ_{inst.upper()}_{i.upper()})"
                        for i, d in delays)

    conns, obs, bit = [], [], 0
    for i, arg in enumerate(func.args):
        b = portname(arg.name)
        # Each request gets a DIFFERENT live signal: tying them together lets
        # yosys collapse the joins downstream into wires.
        conns.append(f"        .{b}_req(spine_q[{req_base + i}]),")
        if not arg.is_control:
            conns.append(f"        .{b}_data(spine_q[{data_base + bit + arg.width - 1}:"
                         f"{data_base + bit}]),")
            bit += arg.width
        conns.append(f"        .{b}_ack({b}_ack),")
        obs.append(f"{b}_ack")
    for i, res in enumerate(func.results):
        b = portname(res.name)
        # The consumer is a latch bit, never the design's own request: feeding
        # a request back would make every matched delay behind it a cycle, and
        # tighten.py treats a pin on a cycle as a state node.
        conns.append(f"        .{b}_req({b}_req), .{b}_ack(spine_q[{ack_base + i}]),")
        if not res.is_control:
            conns.append(f"        .{b}_data({b}_data),")
        obs.append(f"{b}_req")
        if not res.is_control:
            obs.append(f"^{b}_data")
    conns[-1] = conns[-1].rstrip(",")

    decls = []
    for a in func.args:
        decls.append(f"    wire {portname(a.name)}_ack;")
    for r in func.results:
        decls.append(f"    wire {portname(r.name)}_req;")
        if not r.is_control:
            decls.append(f"    wire [{r.width - 1}:0] {portname(r.name)}_data;")

    return f"""
// Matched-delay lengths.  PLACEHOLDERS, exactly as verify/soak_top.v's are,
// and deliberately generous: tighten.py tightens and never pads, so a delay
// that has to GROW after routing is a bundling violation rather than a sizing
// result.
//
// The `include is half the mechanism and leaving it out fails SILENTLY --
// flow.sh accepts BD_SIZES, says it is using measured lengths, copies the file
// in, passes -DBD_SIZES, and nothing includes it.  Every gate then passes on a
// design that ignored its own measurements.
//
// Each key is named after the INSTANCE PATH, because that is what
// verify/tighten.py calls it: macro('{inst}.umux0') -> BD_SZ_{inst.upper()}_UMUX0.
// A key named after the module would be proposed by resize.sh, written to
// sizes.vh, read by nothing, and the loop would report success having changed
// nothing.
`ifdef BD_SIZES
 `include "sizes.vh"
`endif
{defines}

`default_nettype none
module {name}_top (input wire pin_in, output wire pin_out);

    wire rst = pin_in;

    // A free-running spine: the pipe acknowledges itself, so nothing settles
    // and its {nb} latch bits keep changing.  Its latches are keep'd LUT
    // feedback loops and so are opaque to constant folding, which is the only
    // reason the datapath below survives synthesis.
    wire        p_ack_in, p_req_out;
    wire [{nb - 1}:0] spine_q;
    wire        spine;
    bd_delay #(.N(3)) uspin (.a(p_ack_in), .z(spine));

    bd_pipe #(.W({nb}), .N(4)) upipe (
        .rst(rst),
        .req_in(~spine), .ack_in(p_ack_in),
        .data_in({{{nb - 1}'h{seed:x}, pin_in}}),
        .req_out(p_req_out), .ack_out(p_req_out), .data_out(spine_q));

{chr(10).join(decls)}

    {name} #(
{params}) {inst} (
        .rst(rst),
{chr(10).join(conns)});

    // EVERY output is observed, requests included.  An output nobody reads is
    // an output yosys deletes, and a deleted request takes its whole matched
    // delay with it -- after which tighten.py measures a cell with no delay in
    // it and calls that a violation.
    assign pin_out = p_req_out ^ {' ^ '.join(obs)};
endmodule
`default_nettype wire
"""


def generate(path, table=None, top=True):
    """One .mlir file -> one Verilog string containing everything it needs."""
    funcs = [f for f in parse.parse_module(open(path).read(), filename=path)
             if not f.is_declaration]
    if len(funcs) != 1:
        raise EmitError(f"{path}: expected exactly one defined handshake.func, "
                        f"found {len(funcs)}")
    func = funcs[0]
    body, units, delays = emit_func(func, table)
    parts = ["// Generated by bdc/emit.py from " + path,
             "// DO NOT EDIT -- regenerate instead.",
             "`default_nettype none"]
    parts.extend(units[k] for k in sorted(units))
    parts.append(body)
    parts.append("`default_nettype wire")
    if top:
        parts.append(emit_top(func, delays))
    return "\n".join(parts), func, delays


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("mlir")
    ap.add_argument("-o", "--out", help="write here instead of stdout")
    ap.add_argument("--no-top", action="store_true",
                    help="emit the kernel module only, without the two-pin top")
    ap.add_argument("--probe", default="", metavar="CHAN[,CHAN...]",
                    help="bring these internal channels out as read-only "
                         "probe ports (names as they appear in the emitted "
                         "Verilog, e.g. n136_u); also settable as BDC_PROBE")
    args = ap.parse_args()

    if args.probe:
        PROBE[:] = [p for p in args.probe.split(",") if p]

    text, func, delays = generate(args.mlir, top=not args.no_top)
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
        print(f"wrote {args.out}: module bdc_{func.name}, "
              f"{len(delays)} matched delay(s)")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
