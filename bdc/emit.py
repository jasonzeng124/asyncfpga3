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
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import compute  # noqa: E402
from hs import parse  # noqa: E402
from map import Table, Unmapped  # noqa: E402


class EmitError(Exception):
    """A construct this emitter will not guess at.  Always names the op."""


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


def result_channels(node, operand_ch):
    """The (width, is_control) of each of `node`'s results.

    Explicitly per-op.  A generic rule does not exist -- `cmpi`'s type clause
    spells its OPERAND type and never mentions the i1 it produces, while
    `control_merge`'s spells both results after a `to`.  Anything not listed
    raises by name.
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
    if op in ("br", "merge", "buffer"):
        return [operand_ch[0]]
    if op == "mux":
        return [operand_ch[1]]
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


def emit_amerge(width):
    """The two-input arbitrated data merge, as a module."""
    dw = max(width, 1)
    data_ports = "" if width == 0 else f"""
     input  wire [{dw - 1}:0]     x_data,"""
    return AMERGE_HEADER + f"""
(* keep_hierarchy *)
module bdc_amerge_{width} #(parameter DELAY = 4)
    (input  wire             rst,

     input  wire             x_req,
     output wire             x_ack,
     input  wire [{dw - 1}:0]{'     ' if dw > 9 else '      '}x_data,

     input  wire             y_req,
     output wire             y_ack,
     input  wire [{dw - 1}:0]{'     ' if dw > 9 else '      '}y_data,

     output wire             z_req,
     input  wire             z_ack,
     output wire [{dw - 1}:0]{'     ' if dw > 9 else '      '}z_data,

     output wire             grant);

    wire r0, g1, g2;
    bd_arbiter uarb (
        .rst(rst),
        .r1(x_req), .A1(x_ack),
        .r2(y_req), .A2(y_ack),
        .R0(r0),    .A0(z_ack),
        .g1(g1),    .g2(g2));

    // z = g2 ? y : x, matching bd_datamux's own z = s ? b : a.
    bd_datamux #(.W({dw})) udat (.a(x_data), .b(y_data), .s(g2), .z(z_data));

    // Which input won, as ordinary channel data.  This is what a
    // control_merge's index result is, and it is stable for exactly as long
    // as z_data is, because it is the same grant that selected it.
    assign grant = g2;

    wire either;
    (* keep *) LUT1 #(.INIT(2'h2)) uor (.I0(r0), .O(either));
    bd_delay #(.N(DELAY)) udly (.a(either), .z(z_req));

    // g1 is read so the arbiter's own output cannot be optimised away; the
    // grants are a fractured pair and deleting one changes the cell that
    // cells/verify/MTBF.md characterised.
    wire unused_g1 = g1;
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


def link_sites(func, channels):
    """Which channels get a bd_link, as a set of SSA names.

    Swap this function to change the storage policy.  Three alternatives were
    on the table and this is the cheap end of them: storage on every data
    channel (simplest, most area), storage where the uncut combinational depth
    exceeds a threshold (needs a route to decide, so it becomes an
    iterate-until-it-passes loop), or storage at basic-block boundaries (cheap,
    but nothing bounds the within-block path).

    Expect to revisit this against measurements rather than argument.  Nothing
    downstream depends on which rule it is -- the emitter asks this function
    and wires up whatever it says.
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
        # Channels with storage on them.  A linked channel has TWO net
        # bundles: the producer drives `<v>_u_*` and the link drives `<v>_*`,
        # so consumers need no idea whether a link is there.
        self.linked = link_sites(func, self.ch)

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
                ops = node.operands
                if any(o not in self.ch for o in ops):
                    progress.append((i, node))
                    continue
                widths = result_channels(node, [self.ch[o] for o in ops])
                if len(widths) != len(node.results):
                    raise EmitError(
                        f"{node.op} at line {node.src_line}: width rule gave "
                        f"{len(widths)} result type(s) for {len(node.results)} "
                        f"result(s)")
                for name, w in zip(node.results, widths):
                    self.ch[name] = w
            if len(progress) == len(pending):
                stuck = {n.op for _, n in progress}
                raise EmitError(
                    f"could not resolve channel widths; {len(progress)} op(s) "
                    f"left, kinds {sorted(stuck)}. An operand has no producer, "
                    f"which materialize should have made impossible")
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
        """One bd_link per linked channel, between producer and consumer."""
        for ssa in sorted(self.linked):
            w = self.width(ssa)
            inst = f"ulink_{vname(ssa)}"
            d = self.delay(inst, 0)
            self.emit(f"    bd_link #(.W({max(w, 1)}), .DELAY({d})) {inst} (")
            self.emit(f"        .rst(rst),")
            self.emit(f"        .req_in({self.oreq(ssa)}), .ack_in({self.oack(ssa)}), "
                      f".data_in({self.odata(ssa)}),")
            v = vname(ssa)
            self.emit(f"        .req_out({v}_req), .ack_out({v}_ack), "
                      f".data_out({v}_data));")

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

    def _op_merge(self, node, inst):
        ops = node.operands
        if len(ops) == 1:
            self._pass_through(ops[0], node.results[0])
            return
        if len(ops) != 2:
            raise EmitError(
                f"merge with {len(ops)} inputs at line {node.src_line}: only "
                f"the two-input arbitrated merge is built. An N-way merge is a "
                f"tree of them and needs its own arbitration argument made")
        z = node.results[0]
        w = self.width(z)
        self.units.setdefault(f"bdc_amerge_{w}", emit_amerge(w))
        d = self.delay(inst, compute.CELL_DELAY["wide"])
        self.emit(f"    bdc_amerge_{w} #(.DELAY({d})) {inst} (")
        self.emit(f"        .rst(rst),")
        self.emit(f"        .x_req({self.req(ops[0])}), .x_ack({self.ack(ops[0])}), "
                  f".x_data({self.data(ops[0])}),")
        self.emit(f"        .y_req({self.req(ops[1])}), .y_ack({self.ack(ops[1])}), "
                  f".y_data({self.data(ops[1])}),")
        self.emit(f"        .z_req({self.oreq(z)}), .z_ack({self.oack(z)}), "
                  f".z_data({self.odata_out(z)}), .grant());")

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
        if len(ops) != 2:
            raise EmitError(
                f"control_merge with {len(ops)} inputs at line "
                f"{node.src_line}: only two are built. gcd needs three, and "
                f"that is a tree of arbiters plus index encoding -- a real "
                f"design question, not a loop over this code")

        # The arbitrated merge already produces the index as its grant, so
        # result and index leave together and both need forking off one
        # arrival.  The merge's own matched delay covers the grant.
        w = self.width(res)
        self.units.setdefault(f"bdc_amerge_{w}", emit_amerge(w))
        d = self.delay(inst, compute.CELL_DELAY["wide"])
        m_req, m_ack = f"{inst}_req", f"{inst}_ack"
        self.emit(f"    wire {m_req}, {m_ack};")
        if not self.is_control(res):
            self.emit(f"    wire [{max(w, 1) - 1}:0] {inst}_data;")
        self.emit(f"    bdc_amerge_{w} #(.DELAY({d})) {inst} (")
        self.emit(f"        .rst(rst),")
        self.emit(f"        .x_req({self.req(ops[0])}), .x_ack({self.ack(ops[0])}), "
                  f".x_data({self.data(ops[0])}),")
        self.emit(f"        .y_req({self.req(ops[1])}), .y_ack({self.ack(ops[1])}), "
                  f".y_data({self.data(ops[1])}),")
        self.emit(f"        .z_req({m_req}), .z_ack({m_ack}), "
                  f".z_data({inst + '_data' if w else ''}), "
                  f".grant({self.odata(idx)}[0]));")
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
        if len(ins) != 2:
            raise EmitError(
                f"mux with {len(ins)} data inputs at line {node.src_line}: "
                f"bd_mux is two-way. A wider one is a tree plus index "
                f"decoding, which gcd needs and nothing here has designed")
        z = node.results[0]
        w = self.width(z)
        d = self.delay(inst, compute.CELL_DELAY["wide"])
        # s = 0 picks x, so x is input 0 -- the same order the index counts in.
        self.emit(f"    bd_mux #(.W({max(w, 1)}), .DELAY({d})) {inst} (")
        self.emit(f"        .rst(rst),")
        self.emit(f"        .x_req({self.req(ins[0])}), .x_ack({self.ack(ins[0])}), "
                  f".x_data({self.data(ins[0])}),")
        self.emit(f"        .y_req({self.req(ins[1])}), .y_ack({self.ack(ins[1])}), "
                  f".y_data({self.data(ins[1])}),")
        self.emit(f"        .ctl_req({self.req(sel)}), .ctl_ack({self.ack(sel)}), "
                  f".s({self.data(sel)}[0]),")
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
         "    // Function arguments, as channels.",
         "\n".join(bridge),
         "",
         "    // Every internal channel: req and ack always, data unless the",
         "    // channel is control -- a control channel has no data net at",
         "    // all, which is what makes the W=1-tied-low convention free.",
         "\n".join(decls),
         "",
         "\n".join(e.lines),
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
    args = ap.parse_args()

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
