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
import collections
import heapq
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import compute  # noqa: E402
import mem  # noqa: E402

# Delay elements placed per pipeline stage in front of a SELECT (a cond_br
# condition or a mux control).  Overridable so the value can be swept against
# real hardware instead of argued about: BDC_SELECT_PAD=32 python3 bdc/emit.py ...
SELECT_PAD = int(os.environ.get("BDC_SELECT_PAD", "4"))
# Placeholder for a link's acknowledge-fall delay (bd_link.v DACK).  Rule H in
# verify/tighten.py sizes it per route; generous so the placeholder build
# passes and the search only ever shrinks.
ACK_PAD = int(os.environ.get("BDC_ACK_PAD", "6"))
# Placeholder for the request line between two stages of a bd_pipe (SDELAY),
# rule I's knob; the same generous-then-shrink arrangement.
STAGE_PAD = int(os.environ.get("BDC_STAGE_PAD", "3"))
# BDC_MERGE_OUT_LINK=inst[,inst...] (empty by default; the shipped build is byte-identical without it): put one
# bd_link stage between the named arbitrated control_merge (bdc_amerge) and the fork that splits its output into
# result and index, latching the index (and the result's data, if any).  A MEASUREMENT knob for the owner's
# second-latch lead (research/data/itercost/second_latch): the arbiter's output request is its granted input's, so it
# cannot return to zero before that input does; storage on its OUTPUT is the test of whether that is what keeps the
# loop counter ring changing polarity at the merge.  The index is a select, so the link's request delay defaults to
# SELECT_PAD, its acknowledge delay to ACK_PAD (macros DELAY_<INST>_OLINK / _OLINK_UACK; tighten/size them as usual).
MERGE_OUT_LINK = set(filter(None, os.environ.get("BDC_MERGE_OUT_LINK", "").split(",")))
# BDC_MERGE_RES_LINK=inst[,inst...] (empty by default; byte-identical without it): one bd_link on the RESULT branch of
# the named arbitrated merge's output fork (between `<inst>_f` and the result's consumer).  A MEASUREMENT knob for
# PROGRAM.md's 15 ns lead (research/data/fifteen): on xorshift that fork's acknowledge waits for the loop-control steer,
# which waits for the whole counter computation, so the select token's return-to-zero is coupled to the counter's
# rising pass; the timed event graph predicts this one latch removes every polarity change from the critical cycle.
# Request delay DELAY_<INST>_RLINK (default STAGE_PAD), acknowledge delay 0 for a control token (ACK_PAD otherwise).
MERGE_RES_LINK = set(filter(None, os.environ.get("BDC_MERGE_RES_LINK", "").split(",")))
# BDC_RING_COUNT_OLINKS=1 (off by default; byte-identical without it): ring_depths() counts the storage stage that
# BDC_MERGE_OUT_LINK puts on both of a merge's outputs and BDC_MERGE_RES_LINK on its result, so a ring that gets its
# floor of RING_MIN_STAGES from those links no longer needs a deeper bd_pipe elsewhere on it (research/data/fifteen).
RING_COUNT_OLINKS = os.environ.get("BDC_RING_COUNT_OLINKS", "0") == "1"
# BDC_FORK_OUT_LINK=chan[,chan...] (empty by default; byte-identical without it): one bd_link on the named OUTPUT channel
# of a fork (the channel's Verilog base name, e.g. n11__0), between the fork and that output's consumer.  A measurement
# knob for research/data/fifteen: a fork's acknowledge waits for all its consumers, so a consumer that joins with a slow
# token (a loop steer waiting for the loop compare) couples the fork's return-to-zero to that token; the latch decouples
# it.  Request delay DELAY_ULINK_<CHAN>_FOLINK (default STAGE_PAD), acknowledge delay ACK_PAD for data (0 for control).
FORK_OUT_LINK = set(filter(None, os.environ.get("BDC_FORK_OUT_LINK", "").split(",")))
# BDC_FORK_OUT_FASTFALL=1 (off by default; byte-identical without it): RFAST on every BDC_FORK_OUT_LINK link (the fast
# request fall BDC_LINK_FASTFALL gives bare links; rtl/bd_link.v RFAST, audited by verify/tighten.py rule F).  Separate
# from BDC_LINK_FASTFALL so builds made before it keep their emitted text.  research/data/fifteen lever 9: on xorshift
# without the merge olink, the rounds ring's latch on n11__0 binds through its slow request fall.
FORK_OUT_FASTFALL = os.environ.get("BDC_FORK_OUT_FASTFALL", "0") == "1"
# BDC_MERGE_RES_DEPTH=N (default 1; byte-identical at 1): the BDC_MERGE_RES_LINK stage is a bd_pipe of N stages
# (SDELAY DELAY_<INST>_RLINK_SDELAY, default STAGE_PAD).  research/data/fifteen lever 9: without the merge olink, the
# arbiter's output return-to-zero waits for the result latch's, which waits for the loop steer; a second stage lets the
# first empty while the steer holds the second.
MERGE_RES_DEPTH = int(os.environ.get("BDC_MERGE_RES_DEPTH", "1"))
# BDC_SPLIT_SOURCES=1 (off by default; byte-identical without it): a `source` whose token is FORKED to several constants
# (Dynamatic shares one source between the literals of a block: collatz's source2 -> fork5 -> {true, 1 -> fork6 -> five
# readers}) is replaced by one source + constant per reader, so each literal has one reader and compute_fusion folds it
# into its fused region like every unshared literal (no channel, no join input).  Why: the shared fork cannot take the
# next token before EVERY reader has acknowledged, so the readers' return-to-zero is coupled across the loop body;
# research/data/eventgraph/search_all.md (subagent graphsearch): the critical cycle runs through such a fork on 7 of 11
# automatic collatz / ipow / collatz64 routes (0.5-2.9 ns of the period in the timed event graph).  Only where it is the
# same function: every reader is a fused-able op with another operand that is NOT a source's literal (so it fires once
# per arrival of that operand, and an infinite stream of one value in place of another infinite stream of the same value
# changes nothing it computes), or a sink (dropped with its literal: a lone source -> sink pair would oscillate).  A tree
# with any other reader is left as it is.  split_shared_sources() below.
SPLIT_SOURCES = os.environ.get("BDC_SPLIT_SOURCES", "0") == "1"
# BDC_NO_LINK=ulink_<chan>[,...] (empty by default; byte-identical without it): drop the named links from the link set
# before ring_depths() runs, so a ring that needs storage still gets it (ring_depths deepens another link on it, or
# refuses).  A measurement knob for research/data/fifteen: a rule-1 (measurability) link on a loop's ring costs a
# C-element and its request delay every iteration; without it verify/tighten.py loses that start point, and the full
# gate, not the rules, decides whether the design is still correct.
NO_LINK = set(filter(None, os.environ.get("BDC_NO_LINK", "").split(",")))
# BDC_SPEC_INC=inst:k:nshort[,...] (empty by default; byte-identical without it): speculative completion on a fused
# `addi x, 1` unit (research/data/fifteen/speculative.md, Nowick 1996).  The unit gets a second, short request line
# (DELAY_SHORT, sizes key BD_SZ_<INST>_SHORT, default nshort) beside the full one, and a LUT3 picks the long line when
# the low k bits of x are all ones (this increment carries past bit k) or all zeros (the previous one did, and the
# carry chain still has to discharge): abort = &x[k-1:0] | ~|x[k-1:0].  Both lines fall fast from the join.
SPEC_INC = {}
for _item in filter(None, os.environ.get("BDC_SPEC_INC", "").split(",")):
    _i, _k, _n = _item.split(":")
    SPEC_INC[_i] = (int(_k), int(_n))

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

# --host-mem / BDC_HOST_MEM=1: a HOST PORT on every memory, so a test harness
# can fill an array before a call and read it back after one (suiteb,
# 2026-11-17; research/data/suite/bench/README.md).  Off, nothing changes: the
# output is byte-identical to before this existed, and so it is for any kernel
# without a memref argument even when it is on.  On, each mem_controller's
# plain port gets ONE MORE one-hot slot, the last one, wired to six new kernel
# ports per memref argument, in signature order:
#
#     <m>_host_req  in     <m>_host_addr[AW-1:0]  in    <m>_host_we  in
#     <m>_host_ack  out    <m>_host_wdata[DW-1:0] in    <m>_host_rdata[DW-1:0] out
#
# It is the bdc_memport's own slot protocol and nothing else: four-phase on
# req/ack, addr/wdata/we bundled by req, rdata valid while ack is high.  The
# ack is the port's SHARED acknowledge, so the host sees the kernel's accesses
# too -- which is how it can wait for the port to be quiet before it asks.
# No new cell and no arbiter: the one-hot obligation the plain port puts on
# its caller is discharged by the harness, which only drives this slot while
# the kernel is between calls (cells/hw/gen_bench.py refuses a host access
# while a batch is running or the kernel is held in reset).  The port's
# simulation check still fires if anyone breaks that.
HOST_MEM = os.environ.get("BDC_HOST_MEM", "0") == "1"
# BDC_MEM_NOCAP=1: a load on an arbitrated port WITHOUT its capture latch (bdc/mem.py CAPTURE) -- the negative
# control of the load-first lowering (_resolve_mem_accessors), never for a build anyone believes.
MEM_NOCAP = os.environ.get("BDC_MEM_NOCAP", "0") == "1"


# Verilog keywords that a Dynamatic argName/resName can collide with.  `end`
# is not hypothetical: it is the resName of every kernel's completion channel.
RESERVED = {
    "end", "begin", "module", "wire", "reg", "input", "output", "inout",
    "assign", "always", "initial", "parameter", "localparam", "generate",
    "endmodule", "case", "default", "function", "task", "and", "or", "not",
    "buf", "xor", "nand", "nor", "xnor", "if", "else", "for", "while",
}


def host_base(func, memref_ssa):
    """The port base of a memref argument's host port (HOST_MEM): `<m>_host`."""
    for arg in func.args:
        if arg.ssa_name == memref_ssa:
            return portname(arg.name) + "_host"
    raise EmitError(f"memref %{memref_ssa} is not an argument of @{func.name}")


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
    if op in compute.DIV:
        # divui / divsi / remsi (and remui, which Dynamatic's dialect lacks): the dividend's width, as for the
        # other binary ops (HandshakeArithOps.td fixes all three at i32; bdc/compute.py div_datapath is
        # width-generic).
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
    if op in ("load", "store"):
        # `<i10>, <i32>, <i10>, <i32>` -- (addr-in, data-in, addr-out,
        # data-out) atoms in that fixed order regardless of load vs store;
        # the results are always (addressResult, dataResult).  addressResult
        # is absorbed into the owning mem_controller (see _op_load/_op_store)
        # but still needs a real width for the fixpoint.
        atoms = _atoms(node.type_sig)
        if len(atoms) != 4:
            raise EmitError(f"{op} type clause {node.type_sig!r} has "
                            f"{len(atoms)} atom(s), expected 4 (addr-in, "
                            f"data-in, addr-out, data-out)")
        if (op == "store" and len(node.results) == 3
                and node.results[2].endswith(STORE_DONE_SFX)):
            # store_completion_rewrite's third result: the access completing.
            return atoms[2:4] + [CONTROL]
        if len(node.results) != 2:
            raise EmitError(f"{op} at line {node.src_line} has "
                            f"{len(node.results)} result(s), expected 2 "
                            f"(addressResult, dataResult)")
        return atoms[2:4]
    if op == "mem_controller":
        # '(...) -> (...)' -- everything left of '->' is inputs (memref,
        # memStart, the accessor group, ctrlEnd); everything right of it is
        # the data result(s) this controller hands back to its load
        # accessor(s), one atom per result other than the trailing memEnd.
        if not node.results:
            raise EmitError(f"mem_controller at line {node.src_line} has no "
                            f"results; expected at least memEnd")
        n_out = len(node.results) - 1
        parts = node.type_sig.split("->", 1)
        if len(parts) != 2:
            raise EmitError(f"mem_controller at line {node.src_line}: type "
                            f"clause {node.type_sig!r} has no '->' "
                            f"separating inputs from outputs")
        out_atoms = _atoms(parts[1])
        if len(out_atoms) != n_out:
            raise EmitError(f"mem_controller at line {node.src_line}: type "
                            f"clause promises {len(out_atoms)} data "
                            f"result(s), node has {n_out} (results minus "
                            f"memEnd)")
        return out_atoms + [CONTROL]
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
    {compute.request_delay("r0")}

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
    {compute.request_delay("|j")}

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
} | set(compute.DIV)


# ---------------------------------------------------------------------------
# BDC_OP_FUSION -- fuse a maximal region of purely combinational arithmetic
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
# Set BDC_OP_FUSION=0 for the unfused lowering.
#
# It was called BDC_OP_FUSION, which named the smallest thing it does.
# Absorbing a constant is one step INSIDE the transform; the transform itself
# fuses a maximal region of combinational ops into a single cell, and the
# saving is the per-op handshake overhead -- one keep_hierarchy boundary, one
# bd_join, one matched delay, one storage stage each -- not the constants.
# The old name is still accepted so a script or an in-flight build that sets
# it does not silently get the other lowering.
_fusion_env = os.environ.get("BDC_OP_FUSION",
                             os.environ.get("BDC_CONST_FOLD", "1"))
BDC_OP_FUSION = _fusion_env == "1"

# Ops safe to fuse across: DELAY_BEARING minus "mux" -- see the block comment
# above for why "mux" is excluded.
FUSABLE_OPS = DELAY_BEARING - {"mux"} - set(compute.DIV)
# The dividers (compute.DIV) are not fused either: a fused region writes each op as one expression
# (_fused_node_expr), a divider is ~W*W/2 primitives of its own (compute.div_datapath), and its own matched delay
# dwarfs whatever a region would save.  So a divider stays one unit, with its own link in front (DELAY_BEARING).

# Channel-position map for each fusable op.  Exactly _bind_compute's mapping,
# duplicated here (rather than imported from it) because fusion analysis has
# to walk operands before any Emitter, and before any per-op cell, exists.
_FUSABLE_CHANS = {
    op: ({"s": 0, "a": 1, "b": 2} if op == "select" else {"a": 0, "b": 1})
    for op in FUSABLE_OPS
}

BDC_FORK_FUSION = os.environ.get("BDC_FORK_FUSION", "1") == "1"

# BDC_CONST_DATA=1 (OFF by default; the shipped build is byte-identical without it): a fused region reads an
# external operand whose value is a KNOWN constant -- a `constant` node's result, or a fork output whose input is
# one -- as a literal in its datapath, while the channel itself stays: its link, its request in the region's
# bd_join, its acknowledge.  Only the data wire is replaced by the value that wire always carries, so the handshake
# is unchanged and the result is the same function.  Why: constant absorption (compute_fusion) only folds a
# constant fired by a bare `source` with one reader; collatz's shift-by-one (`constant4`, fired by the loop's control
# and forked five ways) is left as a 32-bit data channel, so `n << e1` and `n >>> e3` are synthesised as barrel
# shifters and their matched delays are sized to them (research/data/itercost: 14.6-16.3 ns of excess delay per
# iteration on collatz's critical cycle).
BDC_CONST_DATA = os.environ.get("BDC_CONST_DATA", "0") == "1"
MAX_FUSE_NODES = int(os.environ.get("BDC_MAX_FUSE_NODES", "4"))
BDC_FASTFALL = compute.BDC_FASTFALL
# Opt-in, default off: a fast fall on every bare bd_link's request line (RFAST)
# and every bd_mux's output delay (FASTFALL).  Off emits the same text as
# before, byte for byte.  rtl/bd_link.v RFAST says why it is safe and where it
# is not (bd_pipe, bd_mem); verify/tighten.py rule F audits the drain.
BDC_LINK_FASTFALL = os.environ.get("BDC_LINK_FASTFALL", "0") == "1"

# BDC_AUTO=1 (off by default; unset, nothing below runs and the output is byte-identical): the hand recipes' general
# knobs on, and their instance-named ones replaced by rules over the graph (bdc/auto.py; research/data/auto/README.md).
# A knob set explicitly in the environment wins over what AUTO would choose.  Per function, in Emitter.__init__:
# BDC_MERGE_OUT_LINK + BDC_MERGE_RES_LINK on every loop-header arbitrated control_merge (rule M), BDC_FORK_OUT_LINK on
# every fork output that feeds its loop steer while a sibling feeds that steer's test (rule F), BDC_LINK_FASTFALL where
# the function has no memory port (fast fall is not audited there).  Here: BDC_CONST_DATA and BDC_RING_COUNT_OLINKS.
import auto as _auto  # noqa: E402
_ENV_MO, _ENV_MR, _ENV_FO = set(MERGE_OUT_LINK), set(MERGE_RES_LINK), set(FORK_OUT_LINK)
if _auto.AUTO:
    if "BDC_CONST_DATA" not in os.environ:
        BDC_CONST_DATA = True
    if "BDC_RING_COUNT_OLINKS" not in os.environ:
        RING_COUNT_OLINKS = True


def _auto_apply(func):
    """BDC_AUTO's per-function choices, written into the module knobs the emitter already reads."""
    global MERGE_OUT_LINK, MERGE_RES_LINK, FORK_OUT_LINK, BDC_LINK_FASTFALL
    hdr = _auto.loop_header_merges(func, instname)
    if "BDC_MERGE_OUT_LINK" not in os.environ:
        MERGE_OUT_LINK = _ENV_MO | hdr
    if "BDC_MERGE_RES_LINK" not in os.environ:
        MERGE_RES_LINK = _ENV_MR | hdr
    if "BDC_FORK_OUT_LINK" not in os.environ:
        FORK_OUT_LINK = _ENV_FO | _auto.steer_fork_outputs(func, vname)
    if "BDC_LINK_FASTFALL" not in os.environ:
        BDC_LINK_FASTFALL = not _auto.has_memory(func)
    print(f"auto: {func.name}: merge out/res links {sorted(MERGE_OUT_LINK)} / {sorted(MERGE_RES_LINK)}; "
          f"fork out links {sorted(FORK_OUT_LINK)}; link fast fall {int(BDC_LINK_FASTFALL)}; "
          f"const data {int(BDC_CONST_DATA)}; ring counts olinks {int(RING_COUNT_OLINKS)}", file=sys.stderr)


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


def _topo_order(nodes, members, value_producer, member_set, aliases):
    """`members`, ordered so every node follows every in-region producer of
    its operands.  A plain DFS postorder: fusable regions cannot contain a
    cycle (a cycle needs a mux/control_merge to close, and those are never
    fusable), so this always terminates and is always a valid order."""
    deps = {}
    for i in members:
        d = []
        for opnd in nodes[i].operands:
            p = value_producer.get(aliases.get(opnd, opnd))
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


def _build_region(func, members, value_producer, value_consumers, const_of,
                  aliases=None, known=None):
    aliases = aliases or {}
    nodes = func.nodes
    member_set = set(members)
    region = Region(_topo_order(nodes, members, value_producer, member_set,
                               aliases))

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
                f"BDC_OP_FUSION: fusable op {nodes[i].op!r} at line "
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
            f"BDC_OP_FUSION: fused region "
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
            opnd = aliases.get(n.operands[pos], n.operands[pos])
            p = value_producer.get(opnd)
            if p in member_set:
                region.ref[(i, port)] = ("wire", p)
                continue
            if opnd not in ext_index:
                ext_index[opnd] = len(region.ext_inputs)
                region.ext_inputs.append(opnd)
            region.ref[(i, port)] = ("ext", ext_index[opnd])
            if known and opnd in known:
                # BDC_CONST_DATA: the channel stays an external input (joined, linked, acknowledged); only its data
                # wire is read as the literal it always carries.
                region.ref[(i, port)] = ("const", known[opnd])

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


def _absorb_forks(nodes, uf, value_producer, value_consumers, max_nodes):
    """Contract forks whose entire fanout reconverges in one arithmetic region."""
    owners = {}
    pending = {i for i, n in enumerate(nodes) if n.op == "fork"}

    def owner(i):
        if i in uf.parent:
            return uf.find(i)
        if i in owners:
            return uf.find(owners[i])
        return None

    changed = True
    while changed:
        changed = False
        for i in sorted(pending):
            n = nodes[i]
            if len(n.operands) != 1 or not n.results:
                continue
            if value_consumers.get(n.operands[0]) != [i]:
                continue
            consumers = [value_consumers.get(r, []) for r in n.results]
            if any(len(cs) != 1 for cs in consumers):
                continue
            targets = {owner(cs[0]) for cs in consumers}
            if None in targets or len(targets) != 1:
                continue
            target = targets.pop()
            source = owner(value_producer.get(n.operands[0]))
            if source == target:
                continue
            owners[i] = target
            pending.remove(i)
            changed = True
            if source is not None:
                uf.union_if(source, target, max_nodes)

    aliases = {r: nodes[i].operands[0] for i in owners for r in nodes[i].results}
    for value in aliases:
        src = aliases[value]
        while src in aliases:
            src = aliases[src]
        aliases[value] = src
    return owners, aliases


def compute_fusion(func, *, forks=None, max_nodes=None):
    """BDC_OP_FUSION's whole analysis: which nodes fuse, which constants
    fold.  Pure graph analysis -- no widths needed, so this can run before
    Emitter._resolve_widths, and does not depend on the Emitter at all.
    """
    forks = BDC_FORK_FUSION if forks is None else forks
    max_nodes = MAX_FUSE_NODES if max_nodes is None else max_nodes
    if max_nodes < 1:
        raise EmitError("BDC_MAX_FUSE_NODES must be at least 1")
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
    # and because BDC_OP_FUSION is now something a default build can turn on.
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
        if value_consumers.get(n.operands[0]) != [i]:
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
        uf.union_if(p, c, max_nodes)

    fork_owners, aliases = {}, {}
    if forks:
        fork_owners, aliases = _absorb_forks(
            nodes, uf, value_producer, value_consumers, max_nodes)
        value_consumers = {}
        for i, n in enumerate(nodes):
            if i in fork_owners:
                continue
            for opnd in n.operands:
                value = aliases.get(opnd, opnd)
                value_consumers.setdefault(value, []).append(i)

    groups = {}
    for i in fusable:
        groups.setdefault(uf.find(i), []).append(i)

    known = {}
    if BDC_CONST_DATA:
        changed = True
        while changed:
            changed = False
            for n in nodes:
                if n.op == "constant" and n.results[0] not in known:
                    value = n.attrs.get("value")
                    raw = getattr(value, "value", value)
                    if isinstance(raw, int) and not isinstance(raw, bool):
                        known[n.results[0]] = raw; changed = True
                elif n.op == "fork" and n.operands and n.operands[0] in known:
                    for r in n.results:
                        if r not in known:
                            known[r] = known[n.operands[0]]; changed = True
    plan = FusionPlan()
    plan.skip |= absorbed | fork_owners.keys()
    for members in groups.values():
        region = _build_region(func, members, value_producer, value_consumers,
                                const_of, aliases, known)
        for i in region.node_ids:
            plan.region_of[i] = region
            if i != region.anchor:
                plan.skip.add(i)
                plan.dead_values.add(nodes[i].results[0])
        plan.anchor_region[region.anchor] = region
    for i in absorbed:
        plan.dead_values.add(nodes[i].results[0])
    for i, target in fork_owners.items():
        plan.region_of[i] = plan.region_of[uf.find(target)]
        plan.dead_values.update(nodes[i].results)
    return plan


def _fused_node_expr(op, width, pred, ports, uniq):
    """One interior node's RHS expression inside a fused region.

    The same per-op logic bdc/compute.py's emit_unit uses for a standalone
    cell -- deliberately kept as a separate copy rather than shared with it,
    so that touching this (BDC_OP_FUSION-only) path can never change what
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
        raise EmitError(f"BDC_OP_FUSION has no fused lowering for {op!r}")
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
    """Rule 1 under BDC_OP_FUSION: storage in front of a fused region's
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


def cycle_sites(func, already, exclude=frozenset()):
    """Rule 2: enough further links that no cycle is left without storage.

    `exclude` names channels this graph edge exists for on paper but that
    have no net in the emitted design -- a load/store's address round trip
    with its owning mem_controller, absorbed entirely inside one station (see
    Emitter._resolve_mem_accessors).  slack.build_node_graph is unaware of
    that absorption; without filtering, this function could pick one of those
    edges as a cycle-breaking site and ask emit_links() to wrap a net that
    _op_load/_op_store never declares.

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
    edges = [e for e in edges if e.value not in exclude]
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
#
# That is the ONE-token case.  A cycle that threads T back edges carries T tokens and needs 2T + 1, and two paths
# between one fork and one join that carry different numbers of tokens need storage too: token_floor() below, which
# runs after ring_depths() and adds only where this floor of three is not enough.
RING_MIN_STAGES = 3

_INF = float("inf")


def ring_depths(func, linked, exclude=frozenset()):
    """How deep each link has to be, so that every cycle clears RING_MIN_STAGES.

    `exclude` -- see cycle_sites(): a mem-accessor round trip absorbed inside
    one station has no net, so it must not be considered a cycle edge here
    either, or the "no linked edge to deepen" check below could fire on a
    2-node mem-only cycle that is not a real wire loop at all.

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
    edges = [e for e in edges if e.value not in exclude]
    n = len(func.nodes)
    depth = {ssa: 1 for ssa in linked}
    extra = collections.defaultdict(int)          # storage that is not a link site (BDC_RING_COUNT_OLINKS)
    if RING_COUNT_OLINKS:
        for i, node in enumerate(func.nodes):
            nm = instname(node, i)
            if len(node.results) == 2 and nm in MERGE_OUT_LINK:
                for r in node.results: extra[r] += 1
            if len(node.results) == 2 and nm in MERGE_RES_LINK:
                extra[node.results[0]] += MERGE_RES_DEPTH

    def lightest_cycle():
        """(weight, [edges round it]) for the lightest cycle, or None."""
        out = {v: [] for v in range(n)}
        for e in edges:
            out[e.producer].append((e.consumer, depth.get(e.value, 0) + extra.get(e.value, 0), e))

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


# ---------------------------------------------------------------------------
# The token floor: RING_MIN_STAGES for a cycle that carries more than one token, and for two paths that carry
# different numbers of tokens between one fork and one join.  A correctness rule, on by default (BDC_TOKEN_FLOOR=0
# turns it off, for negative controls only).  research/data/suite/ringfloor.md has the measurements.
#
# THE MODEL.  A storage stage (bd_link, each stage of a bd_pipe, a merge's olink / rlink, a fork output link) is a
# Muller half buffer, c = C(req_in, ~c_next).  Everything else on a ring is a rendezvous with no storage: a join
# (bd_join, a mux's select with its data, a cond_br's condition with its data, a compute cell's operands) is a
# C-element on the requests; a fork is a C-element on the acknowledges; a steer is two AND gates.  So stage t rises
# when every stage feeding it has risen and every stage it feeds has fallen, and falls in the dual case.  While a loop
# iterates (each mux taking its back edge, each loop steer continuing) that is a marked graph on the stage
# transitions: per stage edge s -> t, the arcs s+ -> t+ and s- -> t- (data forward) and t+ -> s-, t- -> s+ (the
# acknowledge back).  A marked graph is live iff every one of its cycles holds a token, and a cycle's token count never
# changes, so it can be read off one state.
#
# TOKENS.  Take the state at an iteration boundary: one loop-carried value resting on each back edge (a data input of a
# mux / merge / control_merge fed from the same or a later basic block), that stage high and its neighbours low, every
# other stage low.  Per stage edge s -> t exactly one arc holds a token: an acknowledge arc when c_s == c_t, a data arc
# when they differ, and a resting value makes exactly the two stage edges around it differ.  A marked-graph cycle is a
# closed walk over stage edges, each taken with the data (it uses the acknowledge arcs: one token per stage, minus two
# per value resting there) or against it (the data arcs: two per resting value).  With d = the back edges a stage edge
# crosses (0 or 1), its token count is
#     sum over edges walked with the data of (1 - 2d)  +  sum over edges walked against it of 2d,
# which has to be >= 1.
#
# WHAT THAT SAYS.  (1) A directed cycle with S stages that threads T back edges (T tokens) needs S >= 2T + 1: two
# stages per token, plus one to move into.  T = 1 is RING_MIN_STAGES = 3.  kernels/quadrec's a <- b <- c <- d <-
# t(a, b, c, d) ring threads four back edges and had 6 stages; it needs 9.  (2) Two paths from one fork to one join,
# Q crossing K more back edges than P, need 2K stages on Q between the fork and the join (the stage after the join is
# shared by both and is the slot the tokens move into; that is the +1 at a join turnaround below).  This one no cycle
# count sees.  quadrec's loop-condition fork feeds every loop steer, so d -> c (cond_br13 -> a link -> mux4 -> fork5 ->
# cond_br12) and the condition's direct wire to cond_br12 are such a pair with K = 1: with ONE stage on that back
# edge the condition fork cannot return to zero until the next condition token has arrived, and it deadlocks with
# every cycle at 2T + 1 (measured: ring_tokens.py reads +1 and simcheck still hangs).  The fix is two stages on each
# rotation back edge, which is also enough for the ring (4 x 2 + 1 = 9 with the link in front of the adder).
#
# THE WALK, on the node graph (the stage-level walk turns at the stage after a join and the stage before a fork; the
# shared piece in between cancels, except the stage after a join, which counts once: +1).  A state is (channel,
# direction).  Forward along a channel costs stages - 2 x tokens; backward costs 2 x tokens.  Through a node: forward
# from an input to an output, backward from an output to an input; a JOIN turnaround (forward in on one input, back out
# on another) only between inputs that are joined -- not two data inputs of a mux, not two inputs of a merge or
# control_merge (one of them fires); a FORK turnaround (back in on one output, forward out on another) only between
# outputs that leave together -- a fork's, a control_merge's result and index -- not a cond_br's two branches.
# Memory ops are passed through and never turned at (not modelled).  A back edge counts only on a cycle (a mux fed from
# its own basic block in loop-free code is not one).  A loop's ENTRY channels (the inputs of its header muxes / merges /
# control_merges that are not back edges) and EXIT channels (the other branch of every steer on the loop's condition --
# the condition whose steer feeds a back edge, traced back through forks) are not walked, for every loop at once: they
# belong to other modes of the circuit than the iterating one, and a walk that mixes modes is no cycle of any one
# marked graph.  Everything else is walked, across strongly connected components: a loop's body is often several
# (quadrec's rotation is one, its loop-control ring another; the condition fork that feeds every steer joins them in
# one direction only), and the walk that deadlocked quadrec runs through both.  So an inner loop is seen iterating, or
# skipped (its guard's other branch), never passed through in one trip.
#
# THE FLOOR.  Find a walk with token count <= 0 (Bellman-Ford on weights scaled so that "<= 0" is "< 0"), add one
# stage to a link it walks forward -- a back edge first (the token's own channel, and the only link some of these
# walks have), then the link with the fewest stages, then by name -- and repeat.  It runs after ring_depths() and
# only ever adds, so a function where every walk already holds a token emits exactly what it did before.
TOKEN_FLOOR = os.environ.get("BDC_TOKEN_FLOOR", "1") != "0"
# THE PASS-THROUGH MODES (research/data/suite/hangs.md).  The walks above see each loop iterating; an inner loop is never
# walked through its entry and exit, so the circuit between an inner loop's last trip and its next entry -- the outer
# loop's own ring -- was never checked.  For every loop P with a loop nested in it, the floor also walks the graph with
# P iterating and every loop nested in P passed through in one trip (token_graph's `mode`).  A back edge is read from
# where its value comes from, through casts (Dynamatic puts the extui of a loop's initial value in the loop's own header
# block, which made matrix's entry channels look like back edges).  BDC_TOKEN_FLOOR_PASS=0 drops the modes (negative
# controls only).
TOKEN_FLOOR_PASS = os.environ.get("BDC_TOKEN_FLOOR_PASS", "1") != "0"
_TF_PASS_ONLY = ("load", "store", "mem_controller", "lsq")
_TF_CAST = ("extui", "extsi", "trunci")


def _bb(node):
    v = node.attrs.get("handshake.bb")
    try:
        return int(v.value) if v is not None else -1
    except (AttributeError, ValueError):
        return -1


def _tf_structure(func, exclude=frozenset()):
    """The loop structure the token floor's walks read: (every, base_skip, loops).

    every = [(value, producer, consumer, operand, tokens)] for every channel not in `exclude`; base_skip = the entry and
    exit channels of every loop, as (value, consumer, operand) -- the original walk graph walks everything else;
    loops = {header block: {"back", "entry", "exit": sets of (value, consumer, operand), "latch": block}}, one per loop
    (Dynamatic gives each loop one header block and numbers a loop's blocks contiguously, so loop L is nested in loop P
    when P's header block < L's and L's latch block <= P's)."""
    try:
        from . import slack
    except ImportError:
        import slack
    nodes = func.nodes
    edges, _adj = slack.build_node_graph(func)
    adj = collections.defaultdict(set)
    for e in edges:
        if e.value not in exclude:
            adj[e.producer].add(e.consumer)
    comp = {}
    for k, scc in enumerate(slack.tarjan_scc(list(range(len(nodes))), adj)):
        if slack._is_cycle(scc, adj):
            for v in scc:
                comp[v] = k
    producer = {r: i for i, n in enumerate(nodes) for r in n.results}
    passthru = ("extui", "extsi", "trunci", "br")

    def root(v):                                  # a steer's condition, back through forks and pass-throughs
        while v in producer and nodes[producer[v]].op in ("fork", "lazy_fork") + passthru \
                and nodes[producer[v]].operands:
            v = nodes[producer[v]].operands[0]
        return v

    def obb(n):                                   # the block a value comes from: a cast's is its operand's
        while n.op in _TF_CAST and n.operands and n.operands[0] in producer:
            n = nodes[producer[n.operands[0]]]
        return _bb(n)

    every = []                                    # (value, producer, consumer, operand, tokens)
    for i, node in enumerate(nodes):
        for r in node.results:
            if r in exclude:
                continue
            for (c, k) in func.consumers.get(r, []):
                cn = nodes[c]
                tok = int(((cn.op == "mux" and k >= 1) or cn.op in ("merge", "control_merge"))
                          and 0 <= _bb(cn) <= obb(node) and i in comp and comp.get(c) == comp[i])
                every.append((r, i, c, k, tok))
    headers = {c for (_r, _i, c, _k, t) in every if t}
    skip = set()                                  # the loops' entry and exit channels, as (value, consumer, operand)
    cont = collections.defaultdict(set)           # loop condition (root) -> the steer result index that continues
    loops = {}
    cond_loop = {}                                # loop condition (root) -> the loop's header block
    for (r, i, c, k, t) in every:
        cn = nodes[c]
        if not t and c in headers and ((cn.op == "mux" and k >= 1) or cn.op in ("merge", "control_merge")):
            skip.add((r, c, k))                   # entry
        if t:                                     # the steer this back edge leaves, through pass-throughs
            lp = loops.setdefault(_bb(cn), {"back": set(), "entry": set(), "exit": set(), "hdr": set(), "latch": -1})
            lp["back"].add((r, c, k))
            lp["hdr"].add(c)
            v, p = r, i
            while nodes[p].op in passthru and nodes[p].operands and nodes[p].operands[0] in producer:
                v = nodes[p].operands[0]
                p = producer[v]
            lp["latch"] = max(lp["latch"], _bb(nodes[p]))
            if nodes[p].op == "cond_br":
                cont[root(nodes[p].operands[0])].add(nodes[p].results.index(v))
                cond_loop.setdefault(root(nodes[p].operands[0]), _bb(cn))
    for (r, i, c, k, t) in every:
        cn = nodes[c]
        if not t and ((cn.op == "mux" and k >= 1) or cn.op in ("merge", "control_merge")):
            for lp in loops.values():
                if c in lp["hdr"]:
                    lp["entry"].add((r, c, k))
    for i, node in enumerate(nodes):              # exit: every steer on a loop's condition, its other branch
        if node.op != "cond_br":
            continue
        d = cont.get(root(node.operands[0]))
        if d is None or len(d) != 1:
            continue
        other = node.results[1 - next(iter(d))]
        for (c2, k2) in func.consumers.get(other, []):
            skip.add((other, c2, k2))
            hb = cond_loop.get(root(node.operands[0]))
            if hb in loops:
                loops[hb]["exit"].add((other, c2, k2))
    return every, skip, loops


def _tf_nested(loops, p):
    """The header blocks of the loops nested (at any depth) in loop p."""
    return {h for h, lp in loops.items()
            if h != p and h > p and lp["latch"] >= 0 and lp["latch"] <= loops[p]["latch"]}


def tf_pass_modes(func, exclude=frozenset()):
    """The token floor's pass-through modes: the header block of every loop that has a loop nested in it."""
    _every, _skip, loops = _tf_structure(func, exclude)
    return sorted(h for h in loops if _tf_nested(loops, h))


def token_graph(func, linked, depth, exclude=frozenset(), mode=None):
    """The walk graph of the token floor (see the block above).

    Returns (chans, out): chans[i] = (value, producer, consumer, operand, stages, tokens) for every channel walked
    (all but memory-absorbed ones and the loops' entry and exit channels); out[s] = [(s2, weight)] for states
    s = 2 * i (channel i walked forward) and 2 * i + 1 (backward).

    mode = None: every loop iterating (the walks above).  mode = the header block of a loop P: P iterates and every
    loop nested in P passes through in one trip -- its entry and exit channels are walked (no tokens: no value rests
    on them at P's iteration boundary) and its back edges are not -- while every other loop is walked as in mode None.
    That is the circuit between an inner loop's last trip and its next entry, which mode None never walks: matrix's
    inner loop exits, the middle loop's back edge returns to its header, and the inner loop's next entry (its initial
    values, through the header muxes, whose selects come from the inner header's control_merge) has to wait for the
    inner header's previous output to return to zero (research/data/suite/hangs.md)."""
    nodes = func.nodes
    every, skip, loops = _tf_structure(func, exclude)
    if mode is not None:
        inner = _tf_nested(loops, mode)
        skip = set()
        for h, lp in loops.items():
            if h in inner:
                skip |= lp["back"]
            else:
                skip |= lp["entry"] | lp["exit"]
    two_in = {i for i, n in enumerate(nodes) if n.op == "control_merge" and len(n.operands) >= 2}
    olink = {i: 1 for i in two_in if instname(nodes[i], i) in MERGE_OUT_LINK}
    chans, ins, outs = [], collections.defaultdict(list), collections.defaultdict(list)
    for (r, i, c, k, tok) in every:
        if (r, c, k) in skip:
            continue
        node = nodes[i]
        st = depth.get(r, 1) if r in linked else 0
        if node.op in ("fork", "lazy_fork") and vname(r) in FORK_OUT_LINK:
            st += 1
        if i in two_in and r == node.results[0] and instname(node, i) in MERGE_RES_LINK:
            st += MERGE_RES_DEPTH
        j = len(chans)
        chans.append((r, i, c, k, st, tok))
        outs[i].append(j)
        ins[c].append(j)

    def joined(node, k1, k2):
        if node.op in _TF_PASS_ONLY or node.op in ("merge", "control_merge"):
            return False
        if node.op == "mux":
            return (k1 == 0) != (k2 == 0)
        return True

    def together(node):
        return node.op in ("fork", "lazy_fork", "control_merge")

    out = [[] for _ in range(2 * len(chans))]
    for j, (r, p, c, k, st, tok) in enumerate(chans):
        cn, pn = func.nodes[c], func.nodes[p]
        # forward on j, arriving at c through operand k
        for j2 in outs[c]:
            out[2 * j].append((2 * j2, chans[j2][4] - 2 * chans[j2][5] + olink.get(c, 0)))
        for j2 in ins[c]:
            if j2 != j and joined(cn, k, chans[j2][3]):
                out[2 * j].append((2 * j2 + 1, 1 + 2 * chans[j2][5]))
        # backward on j, arriving at p through its result r
        for j2 in ins[p]:
            out[2 * j + 1].append((2 * j2 + 1, 2 * chans[j2][5]))
        if together(pn) and pn.op not in _TF_PASS_ONLY:
            for j2 in outs[p]:
                if j2 != j:
                    out[2 * j + 1].append((2 * j2, chans[j2][4] - 2 * chans[j2][5]))
    return chans, out


def short_walk(chans, out):
    """A closed walk whose token count is <= 0, as (count, [states]), or None.  Bellman-Ford (queue form) on
    weight * M - 1, M = states + 1: a simple cycle of n <= states steps is negative there iff its count is <= 0."""
    n = len(out)
    if n == 0:
        return None
    m = n + 1
    dist, pred, steps = [0] * n, [-1] * n, [0] * n
    queue, inq = collections.deque(range(n)), [True] * n
    hit = None
    while queue and hit is None:
        u = queue.popleft()
        inq[u] = False
        du = dist[u]
        for v, w in out[u]:
            nd = du + w * m - 1
            if nd < dist[v]:
                dist[v], pred[v], steps[v] = nd, u, steps[u] + 1
                if steps[v] >= n:
                    hit = v
                    break
                if not inq[v]:
                    inq[v] = True
                    queue.append(v)
    if hit is None:
        return None
    for _ in range(n):            # walk back onto the cycle itself
        hit = pred[hit]
    cyc, at = [hit], pred[hit]
    while at != hit:
        cyc.append(at)
        at = pred[at]
    cyc.reverse()
    total = 0
    for i, u in enumerate(cyc):
        v = cyc[(i + 1) % len(cyc)]
        total += min(w for v2, w in out[u] if v2 == v)
    return total, cyc


def token_floor(func, linked, depth, exclude=frozenset(), forbid=frozenset()):
    """Deepen links until every walk holds a token (the block above).  A short walk that walks no linked channel
    forward gets a new link (one stage) on one of its forward channels, chosen the same way (a back edge first, then by
    name), never on a channel in `forbid` (no net there: fused away, absorbed into a memory station, BDC_NO_LINK).
    Returns [(value, new depth)] in the order the stages were added; changes `linked` and `depth` in place.  Nothing
    to add, nothing changes."""
    added = []
    modes = [None] + (tf_pass_modes(func, exclude) if TOKEN_FLOOR_PASS else [])
    for _ in range(4 * len(func.nodes) + 16):
        for mode in modes:
            chans, out = token_graph(func, linked, depth, exclude, mode=mode)
            found = short_walk(chans, out)
            if found is not None:
                break
        if found is None:
            return added
        count, cyc = found
        fwd = {chans[s // 2][0] for s in cyc if s % 2 == 0}
        tok = {}
        for (r, _p, _c, _k, _s, t) in chans:
            tok[r] = max(tok.get(r, 0), t)
        cand = sorted((v for v in fwd if v in linked), key=lambda v: (-tok[v], depth.get(v, 1), str(v)))
        if not cand:
            new = sorted((v for v in fwd if v not in forbid and v not in exclude), key=lambda v: (-tok[v], str(v)))
            if not new:
                raise EmitError(
                    f"{func.name}: a walk through "
                    f"{sorted({instname(func.nodes[chans[s // 2][2]], chans[s // 2][2]) for s in cyc})} holds "
                    f"{count} token(s) and has no channel walked forward that can take storage")
            linked.add(new[0])
            depth[new[0]] = 1
            added.append((new[0], 1))
            continue
        depth[cand[0]] = depth.get(cand[0], 1) + 1
        added.append((cand[0], depth[cand[0]]))
    raise EmitError(f"{func.name}: the token floor did not converge")


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


def link_sites(func, channels, fusion=None, exclude=frozenset()):
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
    BDC_OP_FUSION's variant, storage on a fused region's external inputs
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
    return sites | cycle_sites(func, sites, exclude=exclude)


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
# Slack stages: an EMPTY stage behind every feed-forward link.
#
# A bd_link is a half buffer.  Its C node cannot rise again until the stage
# after it has taken the token AND its own request has returned to zero, so
# the cycle it sits on runs through the logic on BOTH sides of it: with cone A
# feeding link L feeding cone B, L's period is about fwd(A) + fwd(B) + the
# handshake.  Fusion made that the bottleneck.  It shrank xorshift to two
# cones and two links, and the routed fast-source interval (7.4 ns) came out
# ABOVE the routed latency (6.8 ns): the pipe was slower than the same logic
# with no storage in it at all, because every token has to clear both cones
# before the next may enter the first.
#
# One empty stage between the cones splits that cycle in two -- fwd(A) + eps
# and eps + fwd(B) -- so the interval drops toward the slower cone alone.  The
# stage costs W/2 latch LUTs, one control LUT and one forward hop of latency,
# and needs no logic of its own; the SDELAY rule-I check covers its request.
#
# Only where there IS logic on both sides.  A link fed straight from a port
# (or by nothing but forks and buffers from one) has fwd(A) = whatever the
# environment takes to answer an ack, which the design cannot shorten and
# which a stage cannot overlap with anything; routed, xorshift cap 8 (one
# cone, one link on the input) with a stage there went 6.3 -> 7.7 ns interval
# and 4.1 -> 5.5 ns latency.  Same for a link that feeds a port with no logic
# after it.  And only on links that are NOT on a cycle: a loop's ring carries
# one token per iteration round its loop-carried dependency, so its
# throughput IS its latency and an extra stage on it is pure cost;
# ring_depths() already puts exactly the depth a ring needs and no more.
#
# BDC_SLACK_STAGES=N is how many stages to add (default 1; 0 turns it off).
SLACK_STAGES = int(os.environ.get("BDC_SLACK_STAGES", "1"))


def _logic_before(func, value, linked, producer):
    """Is a matched-delay cell upstream of `value` with no link in between?"""
    seen, stack = set(), [value]
    while stack:
        v = stack.pop()
        if v in seen or v not in producer:
            continue
        seen.add(v)
        node = func.nodes[producer[v]]
        if node.op in DELAY_BEARING:
            return True
        stack.extend(o for o in node.operands if o not in linked)
    return False


def _logic_after(func, value, linked):
    """Is a matched-delay cell downstream of `value` with no link in between?"""
    seen, stack = set(), [value]
    while stack:
        v = stack.pop()
        if v in seen:
            continue
        seen.add(v)
        for ci, _operand in func.consumers.get(v, []):
            node = func.nodes[ci]
            if node.op in DELAY_BEARING:
                return True
            stack.extend(r for r in node.results if r not in linked)
    return False


def slack_sites(func, linked, exclude=frozenset()):
    """The linked channels that sit between two pieces of logic and on no
    cycle, as a set of SSA names."""
    try:
        from . import slack
    except ImportError:
        import slack
    edges, adj = slack.build_node_graph(func)
    ids = list(range(len(func.nodes)))
    comp = {}
    for k, scc in enumerate(slack.tarjan_scc(ids, adj)):
        if slack._is_cycle(scc, adj):
            for v in scc:
                comp[v] = k
    cyclic = {e.value for e in edges
              if e.producer in comp and comp[e.producer] == comp.get(e.consumer)}
    producer = {r: i for i, n in enumerate(func.nodes) for r in n.results}
    return {v for v in linked
            if v not in cyclic and v not in exclude
            and _logic_before(func, v, linked, producer)
            and _logic_after(func, v, linked)}


def _apply_slack_stages(func, linked, depth, exclude=frozenset()):
    if SLACK_STAGES <= 0:
        return set()
    sites = slack_sites(func, linked, exclude)
    for ssa in sites:
        depth[ssa] = depth.get(ssa, 1) + SLACK_STAGES
    return sites


# Per-link stage counts, for slack-matching experiments: BDC_LINK_DEPTHS=
# "ulink_n_v9=2,ulink_n_x=3".  A depth may only be raised -- ring_depths()'s
# answer is a floor the design does not work under.
LINK_DEPTHS = {}
for _item in filter(None, os.environ.get("BDC_LINK_DEPTHS", "").split(",")):
    _k, _, _v = _item.partition("=")
    LINK_DEPTHS[_k.strip()] = int(_v)


def _apply_link_depths(func, linked, depth, floor):
    for ssa in linked:
        want = LINK_DEPTHS.get(f"ulink_{vname(ssa)}")
        if want is None:
            continue
        if want < floor.get(ssa, 1):
            raise EmitError(f"{func.name}: BDC_LINK_DEPTHS asks for {want} "
                            f"stage(s) on ulink_{vname(ssa)}, under the "
                            f"{floor[ssa]} its rings need")
        depth[ssa] = want


# ---------------------------------------------------------------------------
# Results no call bounds: joined with the control results the call does bound
#
# A `source` offers a token forever (cells/rtl/bd_end.v: req = ~ack).  Inside a function that is harmless wherever an
# op joins the source's token with one that came from an argument -- the literal operand of an addi waits for the
# other operand, so it fires once per call.  It is not harmless where a source's tokens reach a function RESULT
# without any such join: bdc lowered `end` to wires, so that port produced tokens with no call at all.  Two of
# Dynamatic's tests do it (kernels/SUITE.md, suitew item 2): test_int16 (`return -1`: out0 = constant(source), 94162
# tokens in 400 us for one start) and unused_arg (the frontend drops the unread memref `a` and drives its memEnd,
# a_end, from a source: with the bench's acknowledge delay that is a ring oscillator, which the rule refuses as a
# combinational cycle with no storage).
#
# What Dynamatic means.  Its `end` is the function's terminator, its operands ARE the results, and it has no RTL (wires
# in its export); a source-fed result is simply valid on every clock.  Its testbench (tools/hls-verifier, HlsTb.cpp)
# sends start once and takes the call's outputs TOGETHER: one tb_join over the valid of every result and every control
# output (memory ends, end), whose ready goes back to all of them.  So a source-fed result is consumed exactly once per
# call, when the call's other outputs are there.  bdc's bench takes each output alone (out0 is captured as the call's
# completion, `end` and every <m>_end go to their own sinks), so the join has to be in the circuit: a result no call
# bounds is joined (bd_join, a C-element with reset) with a copy (bd_fork) of every CONTROL result the call does bound
# -- `end` and each memory's end.  Not start alone: Dynamatic's `end` IS start (in all 104 fixtures that parse it is the
# start argument through forks only), so joined with it alone a source-fed out0 would tell the bench "done" at the
# call's start, while its loops may still be running (gaussian's out0, a folded constant, is that shape); a memory's end
# comes after the exit block's control token (its ctrlEnd).  Not the data result: the bench takes it on its own, and a
# control result's timing beyond once per call does not matter to the bench.  Data, if any, is wired through: it is
# valid from the result's own request until its acknowledge, which is the joined channel's acknowledge, so the bundling
# holds with no delay (a constant is valid forever).  The bd_src now sits behind a consumer that resets
# (COMPILER-PLAN.md asks that of it).
#
# "No call bounds" is decided on tokens, not on reachability: a source reaches a result in 103 of the 104 fixtures
# that parse (every literal operand of every kernel), and nearly all of those are bounded by the op the literal
# feeds.  free_running() is the least fixpoint of: a source is free; a fork / constant / br / reshape / load is free
# when its (first) operand is (a load fires once per address); a join of channels (every compute op, the dividers bdc
# does not lower yet included, cmpi, select, cond_br, join, store, mem_controller) when ALL its operands are; a merge /
# control_merge when ANY is (one free input floods it); a mux when its select and any data input are.  Function
# arguments are never free.  An op not in that table with a free operand stops the emitter (do not assume).
#
# BDC_CALL_JOIN=0 restores the old wiring, byte for byte (the negative control).  A kernel with no free result emits
# exactly what it did before either way.
CALL_JOIN = os.environ.get("BDC_CALL_JOIN", "1") != "0"
_CJ_FIRST = ("constant", "fork", "lazy_fork", "br", "buffer", "trunci", "extui", "extsi", "load")
_CJ_ALL = ("join", "cond_br", "select", "cmpi", "addi", "subi", "muli", "andi", "ori", "xori", "shli", "shrsi",
           "shrui", "divsi", "divui", "remsi", "remui", "store", "mem_controller")
_CJ_ANY = ("merge", "control_merge")


def free_running(func):
    """The SSA values whose tokens no call bounds (see the block comment above)."""
    free = set()
    changed = True
    while changed:
        changed = False
        for node in func.nodes:
            if not node.results or node.results[0] in free:
                continue
            f = [o in free for o in node.operands]
            if node.op == "source":
                hit = True
            elif node.op in _CJ_FIRST:
                hit = bool(f) and f[0]
            elif node.op in _CJ_ALL:
                hit = bool(f) and all(f)
            elif node.op in _CJ_ANY:
                hit = any(f)
            elif node.op == "mux":
                hit = bool(f) and f[0] and any(f[1:])
            elif any(f):
                raise EmitError(f"line {node.src_line}: {node.op!r} reads a channel no call bounds (a source's) and "
                                f"free_running() has no rule for it -- add one, do not assume")
            else:
                hit = False
            if hit:
                free.update(node.results)
                changed = True
    return free


def call_join_plan(func, end_node):
    """([indices of the control results the call bounds], [indices of the results no call bounds]), or None when
    every result is bounded."""
    free = free_running(func)
    joined = [i for i, v in enumerate(end_node.operands) if v in free]
    if not joined:
        return None
    tied = [i for i, (r, v) in enumerate(zip(func.results, end_node.operands)) if r.is_control and v not in free]
    if not tied:
        raise EmitError(f"@{func.name}: result(s) {[func.results[i].name for i in joined]} take tokens from a source "
                        f"with no call bounding them, and no control result is bounded by the call to join them with")
    return tied, joined


# Stores: the completion obligation (research/data/suite/stores.md)
#
# WHAT DYNAMATIC PROMISES.  A controller that owns a store (dynamatic's
# mem_controller_loadless.v + mc_control in data/verilog/support/mc_support.v)
# raises memEnd only when (1) ctrlEnd has arrived -- no more accesses will
# come, (2) remainingStores == 0 and (3) no count token is being presented
# this cycle.  remainingStores is a clocked up/down counter: every basic block
# that holds stores sends the controller one COUNT token per execution,
# carrying how many stores that execution will make (the `constant` operands
# in the accessor list), and every store the controller performs subtracts
# one.  The function's `end` then waits for every memEnd.  So: the call
# returns only after every store it made has reached the RAM.
#
# WHY NOT A COUNTER HERE.  There is no clock to run one on.  An asynchronous
# up/down counter needs an arbitrated merge of the +k and -1 streams (they
# arrive concurrently), an accumulator ring and a steer -- and it would still
# be wrong: the count token of a block's LAST execution and ctrlEnd leave the
# same control fork on different paths, so nothing makes the count arrive
# first, and a count still in flight when ctrlEnd finds the counter at 0 lets
# memEnd fire early.  Dynamatic carries that race in clocked form (ctrl_ready
# is tied to 1; nothing orders count tokens against ctrlEnd).
#
# WHAT IS BUILT INSTEAD: THE STORE'S COMPLETION JOINS THE CONTROL FLOW.  A
# basic block executes every op in it exactly once per execution, so each
# execution of block B makes exactly one completion (the station's z: the RAM
# answered) per store in B.  Join those completions into B's OUTGOING control
# token -- the control-typed operand of B's terminator (br / cond_br) -- and
# the successor block cannot start until B's stores have landed.  Control is
# a single token passing from block to block, so every block execution lies
# on the causal chain that ends at the exit block, whose control is ctrlEnd:
# ctrlEnd is therefore after every store of the call, by construction and not
# by a race, and memEnd = join(memStart held, ctrlEnd) -- the load-only
# lowering, unchanged -- is correct.  The exit block has no terminator; a
# store there is joined into its own controller's ctrlEnd instead.
#
# The count tokens carry nothing this does not already know: checked here,
# each is a compile-time constant equal to its block's number of stores on
# that controller (one count per block, none for a block without stores), and
# then sunk at the controller (bd_snk), so their producers are not stalled.
#
# The rewrite is done on the graph (a `join` node, a third result on each
# store), BEFORE every analysis, so link_sites / ring_depths / token_floor see
# the new edges and the new cycles through the stores.
#
# Its cost: a block's successor waits for the block's stores, so control can
# no longer run ahead of them.  Its by-product: every access of the next block
# execution whose operands depend on that execution's control token (its
# control_merge / merge firing) is after this execution's stores.  Neither is
# Dynamatic's behaviour (Dynamatic lets control run ahead and needs an LSQ
# where accesses may alias across iterations); stores.md says what is shown.
#
# And the function's results: bdc's `end` drives each result port straight
# from its operand, so a kernel's out0 could leave before its memEnd.  For a
# function with a store, _op_end joins every operand first (Dynamatic's end:
# the call returns when all of them have arrived).
#
# Nothing here runs for a function without a store: its graph and its Verilog
# are what they were.

STORE_DONE_SFX = "_stdone"

# BDC_STORE_NOJOIN=1 -- THE ORDERING NEGATIVE CONTROL (research/data/suite/stores.md): the plan is made and checked,
# the count tokens are sunk and the end join is built, but no completion join is inserted and every store's z is tied
# off as before: memEnd = join(memStart held, ctrlEnd) with nothing ordering ctrlEnd after the stores.  Exists so the
# ordering check (tb_store1.v's store count at out0) can be seen to fail.  Never set it for anything that will be
# believed.
STORE_NOJOIN = os.environ.get("BDC_STORE_NOJOIN", "0") == "1"


def _rebuild_index(func):
    """func.producer / func.consumers after func.nodes changed: the parser's
    own two passes (hs/parse.py _Parser._resolve), so a rewritten function
    looks exactly like one that was parsed that way."""
    producer = {k: v for k, v in func.producer.items()
                if isinstance(v, parse.ArgSource)}
    for ni, n in enumerate(func.nodes):
        for ri, name in enumerate(n.results):
            producer[name] = parse.ResultSource(ni, ri)
    for name in list(producer.keys()):
        if "#" not in name:
            producer.setdefault(f"{name}#0", producer[name])
    consumers = {}
    for ni, n in enumerate(func.nodes):
        for oi, ref in enumerate(n.operands):
            if ref not in producer:
                raise EmitError(f"{func.name}: operand %{ref} of {n.op!r} "
                                f"(line {n.src_line}) has no producer after "
                                f"the store-completion rewrite")
            consumers.setdefault(ref, []).append((ni, oi))
    func.producer, func.consumers = producer, consumers


def _replace_operand(node, old, new):
    hits = 0
    for item in node.arg_items:
        if isinstance(item, parse.OperandSegment):
            for sub in item.items:
                if isinstance(sub, parse.OperandItem) and sub.value == old:
                    sub.value = new
                    hits += 1
    if hits != 1:
        raise EmitError(f"{node.op} at line {node.src_line}: operand %{old} "
                        f"appears {hits} times, expected once")


def _const_value(node):
    v = node.attrs.get("value")
    return getattr(v, "value", v)


def split_shared_sources(func):
    """BDC_SPLIT_SOURCES (see the knob): every source tree (a source, the forks of its token, the constants it fires, the
    forks of their values) with more than one reader becomes one source + constant per reader.  Returns
    [(source name, [reader names])] for the trees rewritten; [] (graph untouched) when there is none.  Idempotent."""
    plan = getattr(func, "_bdc_split_plan", None)
    if plan is not None:
        return plan
    nodes = func.nodes
    cons = collections.defaultdict(list)
    for i, n in enumerate(nodes):
        for k, o in enumerate(n.operands):
            cons[o].append((i, k))
    # every value a source tree carries (a source's token, a fork of it, a constant it fires, a fork of that)
    lit = set()
    for i, n in enumerate(nodes):
        if n.op == "source":
            todo = [n.results[0]]
            while todo:
                v = todo.pop()
                if v in lit:
                    continue
                lit.add(v)
                for (ci, _k) in cons.get(v, []):
                    if nodes[ci].op in ("fork", "constant"):
                        todo += nodes[ci].results
    taken = {r for n in nodes for r in n.results} | {a.ssa_name for a in func.args}
    hnames = {n.attrs.get("handshake.name") for n in nodes}
    drop, new_nodes, plan = set(), [], []
    for si, src in enumerate(nodes):
        if src.op != "source":
            continue
        tree, leaves, ok = {si}, [], True
        todo = [(src.results[0], None)]          # (value, the constant node it carries, or None for the bare token)
        while todo and ok:
            v, c = todo.pop()
            for (ci, k) in cons.get(v, []):
                n = nodes[ci]
                if n.op == "fork":
                    tree.add(ci); todo += [(r, c) for r in n.results]
                elif n.op == "constant" and c is None:
                    tree.add(ci); todo.append((n.results[0], ci))
                elif n.op == "sink":
                    tree.add(ci)
                elif (c is not None and n.op in FUSABLE_OPS and n.operands.count(v) == 1
                      and any(o not in lit for o in n.operands)):
                    leaves.append((ci, v, c))
                else:
                    ok = False
                    break
        if not ok or not any(nodes[t].op == "fork" for t in tree) or not leaves:
            continue
        for j, (ci, v, c) in enumerate(leaves):
            cn = nodes[c]
            sres, cres = f"{src.results[0]}_ss{j}", f"{cn.results[0]}_ss{j}"
            sname = f"{src.attrs.get('handshake.name', 'source')}_ss{j}"
            cname = f"{cn.attrs.get('handshake.name', 'constant')}_ss{j}"
            if {sres, cres} & taken or {sname, cname} & hnames:
                raise EmitError(f"{func.name}: BDC_SPLIT_SOURCES: name {sres} / {cres} / {sname} / {cname} is taken")
            taken |= {sres, cres}; hnames |= {sname, cname}
            sattrs = dict(src.attrs); sattrs["handshake.name"] = sname
            if "handshake.bb" in nodes[ci].attrs:
                sattrs["handshake.bb"] = nodes[ci].attrs["handshake.bb"]
            cattrs = dict(cn.attrs); cattrs["handshake.name"] = cname
            if "handshake.bb" in nodes[ci].attrs:
                cattrs["handshake.bb"] = nodes[ci].attrs["handshake.bb"]
            new_nodes.append(parse.Node(op="source", arg_items=[], results=[sres], attrs=sattrs,
                                        src_line=src.src_line, type_sig=src.type_sig))
            new_nodes.append(parse.Node(
                op="constant", arg_items=[parse.OperandSegment(wrap="", items=[parse.OperandItem(value=sres)])],
                results=[cres], attrs=cattrs, src_line=cn.src_line, type_sig=cn.type_sig))
            _replace_operand(nodes[ci], v, cres)
        drop |= tree
        plan.append((src.attrs.get("handshake.name"), [nodes[ci].attrs.get("handshake.name") for ci, _v, _c in leaves]))
    if plan:
        func.nodes[:] = [n for i, n in enumerate(nodes) if i not in drop] + new_nodes
        _rebuild_index(func)
    func._bdc_split_plan = plan
    return plan


def store_completion_rewrite(func):
    """Join every store's completion into its block's outgoing control token
    (see the block comment above).  Returns the plan, a list of
    (bb, join SSA, host node op, [store names]); [] for a function without a
    store, whose graph is left untouched.  Idempotent per Func object."""
    plan = getattr(func, "_bdc_store_plan", None)
    if plan is not None:
        return plan
    nodes = func.nodes
    producer = {}
    for i, n in enumerate(nodes):
        for r in n.results:
            producer[r] = i

    per_mc = []
    for mi, mc in enumerate(nodes):
        if mc.op != "mem_controller" or len(mc.operands) < 3:
            continue
        stores, counts = [], collections.defaultdict(list)
        for v in mc.operands[2:-1]:
            p = producer.get(v)
            if p is None:
                continue                  # _resolve_mem_accessors names it
            if nodes[p].op == "store" and p not in stores:
                stores.append(p)
            elif nodes[p].op == "constant":
                counts[_bb(nodes[p])].append(nodes[p])
        if not stores:
            continue
        want = collections.Counter(_bb(nodes[s]) for s in stores)
        got = {}
        for bb, cs in counts.items():
            if len(cs) != 1:
                raise EmitError(
                    f"mem_controller at line {mc.src_line}: {len(cs)} store-"
                    f"count constants for block {bb}, expected one")
            got[bb] = _const_value(cs[0])
        if got != dict(want):
            raise EmitError(
                f"mem_controller at line {mc.src_line}: its store-count "
                f"tokens {dict(sorted(got.items()))} (block: value) are not "
                f"one per block equal to that block's stores on it "
                f"{dict(sorted(want.items()))}. The completion join counts "
                f"one store per store op per block execution; a count that "
                f"says otherwise is a shape it does not know")
        per_mc.append((mi, stores))
    if not per_mc:
        func._bdc_store_plan = []
        return []
    if STORE_NOJOIN:
        plan = [(-1, None, "nojoin", [nodes[s].attrs.get("handshake.name") for _, ss in per_mc for s in ss])]
        func._bdc_store_plan = plan
        return plan

    taken = set(producer) | {a.ssa_name for a in func.args}
    hnames = {n.attrs.get("handshake.name") for n in nodes}
    done_of = {}
    by_bb = collections.defaultdict(list)          # bb -> [(mc, store)]
    for mi, stores in per_mc:
        for s in stores:
            st = nodes[s]
            if len(st.results) != 2:
                raise EmitError(f"store at line {st.src_line} has "
                                f"{len(st.results)} result(s), expected 2 "
                                f"(addressResult, dataResult)")
            d = st.results[0] + STORE_DONE_SFX
            if d in taken:
                raise EmitError(f"store at line {st.src_line}: completion "
                                f"name %{d} is already taken")
            st.results.append(d)
            taken.add(d)
            done_of[s] = d
            bb = _bb(st)
            if bb < 0:
                raise EmitError(f"store at line {st.src_line} has no "
                                f"handshake.bb: its block is unknown")
            by_bb[bb].append((mi, s))

    new_nodes, plan = [], []
    for bb in sorted(by_bb):
        terms = [i for i, n in enumerate(nodes)
                 if n.op in ("br", "cond_br") and _bb(n) == bb
                 and _atoms(n.type_sig)[-1] == CONTROL]
        sites = []
        if len(terms) == 1:
            t = nodes[terms[0]]
            sites.append((t, t.operands[-1], sorted(s for _, s in by_bb[bb]),
                          f"stdone_join_bb{bb}"))
        elif not terms:
            # The exit block: nothing follows it but `end`.  Its stores join
            # their own controller's ctrlEnd, which must come from this block.
            for mi in sorted({m for m, _ in by_bb[bb]}):
                mc = nodes[mi]
                old = mc.operands[-1]
                p = producer.get(old)
                if p is None or _bb(nodes[p]) != bb:
                    raise EmitError(
                        f"mem_controller at line {mc.src_line}: block {bb} "
                        f"holds a store and has no control terminator, but "
                        f"the controller's ctrlEnd %{old} does not come from "
                        f"block {bb} -- no edge to order the store before")
                mname = re.sub(r"[^A-Za-z0-9_]", "_",
                               str(mc.attrs.get("handshake.name") or f"mc{mi}"))
                sites.append((mc, old, sorted(s for m, s in by_bb[bb] if m == mi),
                              f"stdone_join_{mname}"))
        else:
            raise EmitError(
                f"block {bb} holds a store and has {len(terms)} control "
                f"terminators ({[nodes[i].attrs.get('handshake.name') for i in terms]}); "
                f"the completion join needs exactly one outgoing control token")
        for host, old, ss, hname in sites:
            if hname in taken or hname in hnames:
                raise EmitError(f"{func.name}: name {hname!r} is already taken")
            ops = [old] + [done_of[s] for s in ss]
            items = [parse.OperandSegment(wrap="", items=[parse.OperandItem(value=v)],
                                          trailing_comma=k < len(ops) - 1)
                     for k, v in enumerate(ops)]
            new_nodes.append(parse.Node(
                op="join", arg_items=items, results=[hname],
                attrs={"handshake.bb": nodes[ss[0]].attrs.get("handshake.bb"),
                       "handshake.name": hname},
                src_line=nodes[ss[0]].src_line,
                type_sig=", ".join(["<>"] * len(ops))))
            _replace_operand(host, old, hname)
            taken.add(hname)
            plan.append((bb, hname, host.op,
                         [nodes[s].attrs.get("handshake.name") for s in ss]))
    func.nodes.extend(new_nodes)
    _rebuild_index(func)
    func._bdc_store_plan = plan
    return plan


# ---------------------------------------------------------------------------
# The emitter

class Emitter:
    def __init__(self, func, table=None):
        self.func = func
        self.table = table or Table()
        self.ch = {}        # ssa name -> (width, is_control)
        self.memrefs = {}   # ssa name -> (aw, dw), disjoint from self.ch --
                             # a memref never gets _req/_ack/_data nets
        self.host_wired = set()   # memrefs whose host port a controller drives (HOST_MEM)
        self.lines = []
        self.delays = []    # (instance, default) in emission order
        self.units = {}     # module name -> source text, for generated cells
        # Stores: each block's outgoing control waits for its stores (see
        # store_completion_rewrite).  First, so that every analysis below --
        # AUTO's rules included -- sees the graph that is built.  [] and no
        # change at all for a function without a store.
        self.store_plan = store_completion_rewrite(func)
        if SPLIT_SOURCES:
            for sname, readers in split_shared_sources(func):
                print(f"emit: split sources: {func.name}: {sname} -> one source per literal of {readers}",
                      file=sys.stderr)
        if _auto.AUTO:
            _auto_apply(func)
        self._resolve_widths()
        # Which load/store/mem_controller SSA results round-trip entirely
        # inside a station -- no net -- and how each accessor and controller
        # wires to its shared port.  Must run before link_sites/ring_depths
        # below, which need to know which graph edges to ignore.
        self._resolve_mem_accessors()
        # BDC_OP_FUSION's analysis: which nodes fuse into one cell, which
        # constants fold into a literal.  None when the flag is off, so every
        # site below that checks `self.fusion` takes its original branch and
        # the emitted Verilog is byte-identical to before this existed.
        self.fusion = compute_fusion(func) if BDC_OP_FUSION else None
        # Channels with storage on them.  A linked channel has TWO net
        # bundles: the producer drives `<v>_u_*` and the link drives `<v>_*`,
        # so consumers need no idea whether a link is there.
        self.linked = link_sites(func, self.ch, fusion=self.fusion,
                                  exclude=self.mem_absorbed)
        leaked_mem = self.linked & self.mem_absorbed
        if leaked_mem:
            raise EmitError(
                f"{func.name}: cycle-breaking or rule 1 wants storage on "
                f"{sorted(leaked_mem)}, which is absorbed into a memory "
                f"station's internal address/data round trip with no "
                f"channel left there")
        if self.fusion is not None:
            # See link_sites()'s BDC_OP_FUSION note: rule 2 cannot legally
            # ask for storage on a value fusion has already folded into a
            # cell with no channel left to put it on.  This has to hold for
            # the emitted Verilog to reference only nets that exist; check it
            # rather than trust the argument that it does.
            leaked = self.linked & self.fusion.dead_values
            if leaked:
                raise EmitError(
                    f"{func.name}: cycle-breaking wants storage on "
                    f"{sorted(leaked)}, which BDC_OP_FUSION folded into a "
                    f"fused cell with no channel left there -- this loop "
                    f"shape is not safe to fuse this way")
        if NO_LINK:
            gone = {v for v in self.linked if f"ulink_{vname(v)}" in NO_LINK}
            if len(gone) != len(NO_LINK):
                raise EmitError(f"{func.name}: BDC_NO_LINK names links that do not exist: "
                                f"{sorted(NO_LINK - {f'ulink_{vname(v)}' for v in gone})}")
            self.linked = set(self.linked) - gone
        # ...and how many stages each of those links is, which is 1 everywhere
        # except on the short cycles that would otherwise sit under the floor.
        self.depth = ring_depths(func, self.linked, exclude=self.mem_absorbed)
        # ...and deeper where a cycle carries more than one token, or two paths between one fork and one join carry
        # different numbers (token_floor()).  Adds nothing where every walk already holds a token.
        self.token_floor = []
        if TOKEN_FLOOR:
            forbid = set(self.mem_absorbed) | {v for v in self.ch if f"ulink_{vname(v)}" in NO_LINK}
            if self.fusion is not None:
                forbid |= set(self.fusion.dead_values)
            self.linked = set(self.linked)
            self.token_floor = token_floor(func, self.linked, self.depth, exclude=self.mem_absorbed, forbid=forbid)
            for v, n in self.token_floor:
                print(f"emit: token floor: {func.name}: ulink_{vname(v)} -> {n} stage(s)", file=sys.stderr)
        floor = dict(self.depth)
        _apply_ring_pad(func, self.linked, self.depth)
        # ...plus one empty stage on every feed-forward link, for throughput.
        self.slack_stages = _apply_slack_stages(func, self.linked, self.depth,
                                                exclude=self.mem_absorbed)
        _apply_link_depths(func, self.linked, self.depth, floor)
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
                # A memref argument parses to Channel(width=0, is_control=False)
                # -- see bdc/hs/parse.py's Channel docstring, where raw carries
                # the truth and width/is_control are just 0/False.  That pair is
                # INDISTINGUISHABLE here from a genuine zero-bit DATA channel,
                # so without this check a `memref<64xi32>` argument becomes a
                # 0-wide data bundle and every load and store hung off it emits
                # wires of width zero.  Nothing downstream complains; the design
                # simply has no memory in it.  Parse its real shape instead --
                # into self.memrefs, never self.ch, so it can never accidentally
                # get _req/_ack/_data nets: a memref is not a channel, it is the
                # address/data width pair its mem_controller and every load and
                # store hung off it need.
                if arg.raw.startswith("memref"):
                    m = re.fullmatch(r"memref<(\d+)x[iu](\d+)>", arg.raw)
                    if not m:
                        raise EmitError(
                            f"function argument %{arg.ssa_name} is "
                            f"{arg.raw!r}, which is not a memref<NxiW> this "
                            f"backend knows how to parse. Add a rule, do not "
                            f"guess a shape.")
                    n_elems, dw = int(m.group(1)), int(m.group(2))
                    aw = max(1, (n_elems - 1).bit_length())
                    mem.check(aw, dw)
                    self.memrefs[arg.ssa_name] = (aw, dw)
                    continue
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

    # -- memory --------------------------------------------------------

    def _resolve_mem_accessors(self):
        """Match each mem_controller to its load/store accessors, in program
        order, and work out the wiring the shared-port design in bdc/mem.py
        needs.

        A load's addressResult, and a store's addressResult/dataResult, are
        the owning station's own p_addr/p_rdata pair: internal to
        bdc_load_<AW>_<DW>/bdc_store_<AW>_<DW>, not a channel in the emitted
        netlist.  So is the mem_controller's own data-output result -- the
        SAME round trip, read from the controller's side, and it is what a
        load's second operand actually is (verified below by producer, not
        guessed by position).  self.mem_absorbed collects every SSA name on
        that round trip; nothing else in this file may declare a net for one.

        self.accessor_info[addr_result_ssa] and self.mc_info[memEnd_ssa] hold
        everything _op_load/_op_store/_op_mem_controller need, keyed by a
        result each op already has in hand -- lower() calls per-op methods as
        fn(node, inst) with no index, so lookups here cannot be keyed by node
        index or by the (unhashable) Node itself.
        """
        nodes = self.func.nodes
        producer, consumers = {}, {}
        for i, n in enumerate(nodes):
            for r in n.results:
                producer[r] = i
            for o in n.operands:
                consumers.setdefault(o, []).append(i)

        self.mem_absorbed = set()
        self.accessor_info = {}
        self.mc_info = {}

        for mc_idx, node in enumerate(nodes):
            if node.op != "mem_controller":
                continue
            ops = node.operands
            if len(ops) < 3:
                raise EmitError(
                    f"mem_controller at line {node.src_line} has "
                    f"{len(ops)} operand(s); expected at least 3 (memref, "
                    f"memStart, ctrlEnd)")
            memref_ssa, memstart, ctrlend = ops[0], ops[1], ops[-1]
            if memref_ssa not in self.memrefs:
                raise EmitError(
                    f"mem_controller at line {node.src_line}: operand "
                    f"{memref_ssa!r} is not a memref this backend resolved "
                    f"a shape for")
            aw, dw = self.memrefs[memref_ssa]

            # ops[2:-1] is the paren-grouped accessor list -- program order,
            # per bdc/AUDIT.md's reading of the dialect.  It also carries a
            # per-basic-block store-count constant (mem_controller_loadless's
            # `remainingStores` increment in dynamatic's mc_support.v); skip
            # those, they name no accessor.
            ordered, seen, counts = [], set(), []
            for v in ops[2:-1]:
                p = producer.get(v)
                if p is None:
                    raise EmitError(
                        f"mem_controller at line {node.src_line}: operand "
                        f"{v!r} has no producer in this function")
                pop = nodes[p].op
                if pop == "constant":
                    # A block's store count: sunk at the controller (see
                    # store_completion_rewrite, which checked its value).
                    counts.append(v)
                    continue
                if pop not in ("load", "store"):
                    raise EmitError(
                        f"mem_controller at line {node.src_line}: operand "
                        f"{v!r} is produced by {pop!r}, which is neither an "
                        f"access (load/store) nor a per-block store count "
                        f"(constant) -- this design does not know what it is")
                if p not in seen:
                    seen.add(p)
                    ordered.append(p)

            n = len(ordered)
            if n == 0:
                raise EmitError(
                    f"mem_controller at line {node.src_line} has no "
                    f"load/store accessor")
            if n > 2:
                raise EmitError(
                    f"mem_controller at line {node.src_line} has {n} "
                    f"accessors; only 1 (plain port) or 2 (arbitrated port -- "
                    f"bd_arbiter arbitrates exactly two requesters) is "
                    f"implemented")
            arb = n == 2
            # LOAD FIRST (LS, LL; mc:load1st, research/data/suite/dyn/README.md).  The program-order token is the
            # first accessor's z, as for a store first -- but a load's z already feeds its consumer, so it is FORKED:
            # the consumer and the second accessor's c both get the request, and the load's z_ack is their
            # C-element (bd_fork), so the load's operands are not released before the second accessor has taken
            # its token.  And every load on this port CAPTURES its word (bdc/mem.py CAPTURE): the second accessor
            # may clock the RAM -- a store writes, WRITE_FIRST rewrites DOADO -- while the load's consumers still
            # read the data, which z_data = p_rdata alone would not survive.  BDC_MEM_NOCAP=1 (a negative control,
            # never for a build anyone believes) leaves the latch out.
            load_first = arb and nodes[ordered[0]].op == "load"
            # The token is one per execution of the first accessor, consumed by one execution of the second: that
            # is program order only when both run once per execution of ONE block.  Accessors in different blocks
            # (binary_search's two loops, iir's load before its loop) execute different numbers of times -- a
            # chain across them deadlocks on the first token the second never takes.  There, as in Dynamatic's own
            # mem_controller (an arbiter, no order), the dataflow orders them and nothing else: both stations are
            # plain, each load captures its word.
            chained = arb and (not load_first or _bb(nodes[ordered[0]]) == _bb(nodes[ordered[1]]))

            if arb and nodes[ordered[0]].op == "store" and len(nodes[ordered[0]].results) == 3:
                raise EmitError(
                    f"mem_controller at line {node.src_line}: a store chained "
                    f"before a load on an arbitrated port. Its completion "
                    f"would have to reach both the load's program-order token "
                    f"and its block's completion join (store_completion_"
                    f"rewrite): a fork that is not built or verified")

            mc_inst = instname(node, mc_idx)
            memend = node.results[-1]

            # The controller's own data-output result(s): the other half of
            # each load's address/data round trip.  Verify each load's
            # second operand really is produced by THIS controller -- not
            # guessed by position -- then absorb it, same as the accessor's
            # own addressResult.
            out_results = list(node.results[:-1])
            claimed = set()
            for acc_idx in ordered:
                acc = nodes[acc_idx]
                if acc.op != "load":
                    continue
                if len(acc.operands) != 2:
                    raise EmitError(
                        f"load at line {acc.src_line} has "
                        f"{len(acc.operands)} operand(s), expected 2 "
                        f"(address, mem_controller readback)")
                out_ssa = acc.operands[1]
                if producer.get(out_ssa) != mc_idx:
                    raise EmitError(
                        f"load at line {acc.src_line}: second operand "
                        f"{out_ssa!r} is not produced by its own "
                        f"mem_controller (line {node.src_line}) -- the "
                        f"address/data round trip this design absorbs does "
                        f"not hold")
                if out_ssa not in out_results:
                    raise EmitError(
                        f"load at line {acc.src_line}: its second operand "
                        f"{out_ssa!r} is not among mem_controller (line "
                        f"{node.src_line})'s own declared results "
                        f"{out_results}")
                claimed.add(out_ssa)
                self.mem_absorbed.add(out_ssa)
            unclaimed = [r for r in out_results if r not in claimed]
            if unclaimed:
                raise EmitError(
                    f"mem_controller at line {node.src_line} declares data "
                    f"result(s) {unclaimed} that no load accessor's second "
                    f"operand claims")

            # Slot wiring.  Only the SECOND station in a 2-way chain gets the
            # program-order token input (bdc/mem.py: "prev.z_req/z_ack ->
            # next.c_req/c_ack" -- the first station is the plain variant, it
            # has no c port to wire).
            tok_req, tok_ack = f"{mc_inst}_tok_req", f"{mc_inst}_tok_ack"
            accessors_desc = []
            for k, acc_idx in enumerate(ordered):
                acc = nodes[acc_idx]
                seq = chained and k > 0
                addr_res = acc.results[0]
                info = {
                    "aw": aw, "dw": dw, "seq": seq, "slot": k,
                    "mc_inst": mc_inst,
                    "p_req": f"{mc_inst}_s{k}_req",
                    "p_ack": f"{mc_inst}_s{k}_ack",
                    "p_addr": f"{mc_inst}_s{k}_addr",
                    "p_wdata": f"{mc_inst}_s{k}_wdata",
                    "p_we": f"{mc_inst}_s{k}_we",
                    "p_rdata": f"{mc_inst}_rdata",
                }
                if chained and k == 0 and load_first:
                    info["z_fork"] = (tok_req, tok_ack)   # _op_load: z -> {its consumer, the token}
                elif arb and k == 0 and not load_first:
                    info["z_req_net"] = tok_req
                    info["z_ack_net"] = tok_ack
                if arb and acc.op == "load":
                    info["cap"] = not MEM_NOCAP
                if seq:
                    info["c_req"] = tok_req
                    info["c_ack"] = tok_ack
                self.accessor_info[addr_res] = info
                self.mem_absorbed.add(acc.results[0])
                if acc.op == "store":
                    # A third result is store_completion_rewrite's completion
                    # channel: a real channel, not absorbed.
                    if not (len(acc.results) == 2 or (
                            len(acc.results) == 3
                            and acc.results[2].endswith(STORE_DONE_SFX))):
                        raise EmitError(
                            f"store at line {acc.src_line} has "
                            f"{len(acc.results)} result(s), expected 2 "
                            f"(addressResult, dataResult)")
                    self.mem_absorbed.add(acc.results[1])
                accessors_desc.append((acc.op, addr_res))

            self.mc_info[memend] = {
                "aw": aw, "dw": dw, "slots": n, "arb": arb, "chained": chained,
                "inst": mc_inst, "accessors": accessors_desc,
                "memstart": memstart, "ctrlend": ctrlend,
                "memref": memref_ssa, "counts": counts,
            }

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
            # A control channel's link latches a constant: nothing to hold.
            a = self.delay(f"{inst}_uack", 0 if self.is_control(ssa) else ACK_PAD)
            if n > 1:
                # The request line on each internal stage boundary: rule I.
                s = self.delay(f"{inst}_sdelay", STAGE_PAD)
                self.emit(f"    bd_pipe #(.W({max(w, 1)}), .N({n}), "
                          f".DELAY({d}), .SDELAY({s}), .DACK({a})) {inst} (")
            else:
                rf = ", .RFAST(1)" if BDC_LINK_FASTFALL else ""
                self.emit(f"    bd_link #(.W({max(w, 1)}), .DELAY({d}), "
                          f".DACK({a}){rf}) {inst} (")
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
        olink = inst in MERGE_OUT_LINK
        z_req, z_ack, z_dat, z_idx = m_req, m_ack, inst + '_data', f"{self.odata(idx)}[{iw - 1}:0]"
        if olink:
            z_req, z_ack, z_idx = f"{inst}_lreq", f"{inst}_lack", f"{inst}_lidx"
            self.emit(f"    wire {z_req}, {z_ack};")
            self.emit(f"    wire [{iw - 1}:0] {z_idx};")
            if w and not self.is_control(res):
                z_dat = f"{inst}_ldata"
                self.emit(f"    wire [{max(w, 1) - 1}:0] {z_dat};")
        self.emit(f"    bdc_amerge{n}_{w} #(.DELAY({d})) {inst} (")
        self.emit(f"        .rst(rst),")
        for k, o in enumerate(ops):
            self.emit(f"        .in{k}_req({self.req(o)}), "
                      f".in{k}_ack({self.ack(o)}), .in{k}_data({self.data(o)}),")
        self.emit(f"        .z_req({z_req}), .z_ack({z_ack}), "
                  f".z_data({z_dat if w else ''}), "
                  f".index({z_idx}));")
        if olink:
            wd = w if (w and not self.is_control(res)) else 0
            ld = self.delay(f"{inst}_olink", SELECT_PAD)
            la = self.delay(f"{inst}_olink_uack", ACK_PAD)
            din = f"{{{z_dat}, {z_idx}}}" if wd else z_idx
            dout = f"{{{inst}_data, {self.odata(idx)}[{iw - 1}:0]}}" if wd else f"{self.odata(idx)}[{iw - 1}:0]"
            self.emit(f"    bd_link #(.W({iw + wd}), .DELAY({ld}), .DACK({la})) {inst}_olink (")
            self.emit(f"        .rst(rst),")
            self.emit(f"        .req_in({z_req}), .ack_in({z_ack}), .data_in({din}),")
            self.emit(f"        .req_out({m_req}), .ack_out({m_ack}), .data_out({dout}));")
        if self.width(idx) > iw:
            self.emit(f"    assign {self.odata(idx)}"
                      f"[{self.width(idx) - 1}:{iw}] = "
                      f"{self.width(idx) - iw}'d0;")
        rlink = inst in MERGE_RES_LINK
        r_req, r_ack = self.oreq(res), self.oack(res)
        if rlink:
            r_req, r_ack = f"{inst}_rreq", f"{inst}_rack"
            self.emit(f"    wire {r_req}, {r_ack};")
        self.emit(f"    bd_fork #(.N(2)) {inst}_f (")
        self.emit(f"        .rst(rst), .req({m_req}), .ack({m_ack}),")
        self.emit(f"        .req_out({{{self.oreq(idx)}, {r_req}}}),")
        self.emit(f"        .ack_in({{{self.oack(idx)}, {r_ack}}}));")
        if rlink:
            ctl = self.is_control(res)
            rd = self.delay(f"{inst}_rlink", STAGE_PAD)
            ra = self.delay(f"{inst}_rlink_uack", 0 if ctl else ACK_PAD)
            rw = 1 if ctl else max(w, 1)
            rin = "1'b0" if ctl else f"{inst}_data"
            rout = "" if ctl else self.odata(res)
            if MERGE_RES_DEPTH > 1:
                rs = self.delay(f"{inst}_rlink_sdelay", STAGE_PAD)
                self.emit(f"    bd_pipe #(.W({rw}), .N({MERGE_RES_DEPTH}), .DELAY({rd}), .SDELAY({rs}), "
                          f".DACK({ra})) {inst}_rlink (")
            else:
                self.emit(f"    bd_link #(.W({rw}), .DELAY({rd}), .DACK({ra})) {inst}_rlink (")
            self.emit(f"        .rst(rst),")
            self.emit(f"        .req_in({r_req}), .ack_in({r_ack}), .data_in({rin}),")
            self.emit(f"        .req_out({self.oreq(res)}), .ack_out({self.oack(res)}), .data_out({rout}));")
        elif not self.is_control(res):
            self.emit(f"    assign {self.odata(res)} = {inst}_data;")

    def _op_fork(self, node, inst):
        x = node.operands[0]
        n = len(node.results)
        fl = {r for r in node.results if vname(r) in FORK_OUT_LINK}
        rq = {r: (f"{vname(r)}_freq" if r in fl else self.oreq(r)) for r in node.results}
        ak = {r: (f"{vname(r)}_fack" if r in fl else self.oack(r)) for r in node.results}
        for r in node.results:
            if r in fl:
                self.emit(f"    wire {rq[r]}, {ak[r]};")
        reqs = ", ".join(rq[r] for r in reversed(node.results))
        acks = ", ".join(ak[r] for r in reversed(node.results))
        self.emit(f"    bd_fork #(.N({n})) {inst} (")
        self.emit(f"        .rst(rst), .req({self.req(x)}), .ack({self.ack(x)}),")
        self.emit(f"        .req_out({{{reqs}}}), .ack_in({{{acks}}}));")
        # Data is broadcast, which is wiring -- bd_fork routes the handshake
        # and nothing else.
        for r in node.results:
            if r in fl:
                ctl = self.is_control(r)
                li = f"ulink_{vname(r)}_folink"
                d = self.delay(li, STAGE_PAD)
                a = self.delay(f"{li}_uack", 0 if ctl else ACK_PAD)
                w = 1 if ctl else max(self.width(r), 1)
                rf = ", .RFAST(1)" if FORK_OUT_FASTFALL else ""
                self.emit(f"    bd_link #(.W({w}), .DELAY({d}), .DACK({a}){rf}) {li} (")
                self.emit(f"        .rst(rst),")
                self.emit(f"        .req_in({rq[r]}), .ack_in({ak[r]}), .data_in({chr(39).join(['1', 'b0']) if ctl else self.data(x)}),")
                self.emit(f"        .req_out({self.oreq(r)}), .ack_out({self.oack(r)}), .data_out({'' if ctl else self.odata(r)}));")
            elif not self.is_control(r):
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
            ff = ", .FASTFALL(1)" if BDC_LINK_FASTFALL else ""
            self.emit(f"    bd_mux #(.W({max(w, 1)}), .DELAY({d}){ff}) {inst} (")
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
        """The function's results, which are ports, not cells -- except a result no call bounds, which is joined with
        a copy of every control result the call does bound (see free_running() and the block comment above it)."""
        if len(node.operands) != len(self.func.results):
            raise EmitError(
                f"end at line {node.src_line} has {len(node.operands)} "
                f"operand(s) for {len(self.func.results)} function result(s)")
        plan = call_join_plan(self.func, node) if CALL_JOIN else None
        if plan is not None and self.store_plan:
            raise EmitError(f"@{self.func.name}: a function with a store and a result no call bounds -- the stores' "
                            f"completion join and the call join are not combined yet (research/data/suite/stores.md)")
        tied, joined = plan if plan is not None else ([], [])
        base = [portname(r.name) for r in self.func.results]
        if plan is not None:
            fb = ", ".join(base[i] for i in joined)
            what = "this result" if len(joined) == 1 else "these results"
            self.emit(f"    // {fb}: no call bounds {what} (a source's tokens, joined with no argument's): "
                      f"joined with a")
            self.emit(f"    // copy of every control result the call bounds ({', '.join(base[t] for t in tied)}), so "
                      f"each leaves once per call, with them.")
            # One fork per bounded control result: copy 0 to its port, copy j + 1 to free result j's join.
            for t in tied:
                tok = node.operands[t]
                cp = [f"{inst}_{base[t]}_c{j}" for j in range(len(joined))]
                self.emit(f"    wire {', '.join(f'{c}_req, {c}_ack' for c in cp)};")
                reqs = ", ".join([f"{c}_req" for c in reversed(cp)] + [f"{base[t]}_req"])
                acks = ", ".join([f"{c}_ack" for c in reversed(cp)] + [f"{base[t]}_ack"])
                self.emit(f"    bd_fork #(.N({len(joined) + 1})) {inst}_ufork_{base[t]} (")
                self.emit(f"        .rst(rst), .req({self.req(tok)}), .ack({self.ack(tok)}),")
                self.emit(f"        .req_out({{{reqs}}}), .ack_in({{{acks}}}));")
            for j, i in enumerate(joined):
                src = node.operands[i]
                cp = [f"{inst}_{base[t]}_c{j}" for t in tied]
                reqs = ", ".join([f"{c}_req" for c in reversed(cp)] + [self.req(src)])
                acks = ", ".join([f"{c}_ack" for c in reversed(cp)] + [self.ack(src)])
                self.emit(f"    bd_join #(.N({len(tied) + 1})) {inst}_ujoin_{base[i]} (")
                self.emit(f"        .rst(rst), .req_in({{{reqs}}}), .ack_out({{{acks}}}),")
                self.emit(f"        .req({base[i]}_req), .ack({base[i]}_ack));")
                if not self.is_control(src):
                    self.emit(f"    assign {base[i]}_data = {self.data(src)};")
        skip = set(joined) | set(tied)
        if self.store_plan:
            # A function with a store returns its data results only together
            # with the memEnd of every controller that has a store (Dynamatic's
            # end waits for all of them): out0 and memEnd otherwise travel
            # independent paths, and a caller (the bench) that takes out0 as
            # the call's completion would read the array, or start the next
            # call, with a store still in flight.  One join over those
            # operands, one fork to their ports; the data is bundled by the
            # join's request, which rises after the data's own.
            #
            # Only those.  The other control results stay direct, because one
            # of them is typically the start token passed straight through
            # (single_loop: `end ... %0#1`), and holding it would hold the
            # start fork's acknowledge -- and with it the loop header's
            # return to zero -- until the call ends: a deadlock (measured,
            # cells/sim RTL of fill, before this was narrowed).
            stends = {m for m, i in self.mc_info.items()
                      if any(k == "store" for k, _ in i["accessors"])}
            sel = [i for i, s_ in enumerate(node.operands)
                   if not self.is_control(s_) or s_ in stends]
            if len(sel) >= 2:
                n = len(sel)
                reqs = ", ".join(self.req(node.operands[i]) for i in reversed(sel))
                acks = ", ".join(self.ack(node.operands[i]) for i in reversed(sel))
                preqs = ", ".join(f"{base[i]}_req" for i in reversed(sel))
                packs = ", ".join(f"{base[i]}_ack" for i in reversed(sel))
                self.emit(f"    wire {inst}_all_req, {inst}_all_ack;")
                self.emit(f"    bd_join #(.N({n})) {inst}_ujoin (")
                self.emit(f"        .rst(rst), .req_in({{{reqs}}}), .ack_out({{{acks}}}),")
                self.emit(f"        .req({inst}_all_req), .ack({inst}_all_ack));")
                self.emit(f"    bd_fork #(.N({n})) {inst}_ufork (")
                self.emit(f"        .rst(rst), .req({inst}_all_req), .ack({inst}_all_ack),")
                self.emit(f"        .req_out({{{preqs}}}), .ack_in({{{packs}}}));")
                for i in sel:
                    if not self.is_control(node.operands[i]):
                        self.emit(f"    assign {base[i]}_data = {self.data(node.operands[i])};")
                skip.update(sel)
        for i, (res, src) in enumerate(zip(self.func.results, node.operands)):
            if i in skip:
                continue
            self.emit(f"    assign {base[i]}_req = {self.req(src)};")
            self.emit(f"    assign {self.ack(src)} = {base[i]}_ack;")
            if not self.is_control(src):
                self.emit(f"    assign {base[i]}_data = {self.data(src)};")

    # -- memory --------------------------------------------------------

    def _op_load(self, node, inst):
        """A load: its own bdc_load_<AW>_<DW>[_seq] station, driving one
        slot of the mem_controller's shared port.  addressResult is
        absorbed into the controller (see _resolve_mem_accessors) and gets
        no net; operand 1 is that same round trip read back from the
        controller's side and is never referenced here -- it exists only so
        the pre-pass could verify the round trip holds.
        """
        if BDC_LINK_FASTFALL:
            raise EmitError("BDC_LINK_FASTFALL=1 is not audited for a kernel "
                            "with memory: bd_mem samples its request edges, "
                            "and a fast-falling request shortens the RAM "
                            "clock's low phase (rtl/bd_link.v RFAST)")
        if len(node.operands) != 2:
            raise EmitError(
                f"load at line {node.src_line} has {len(node.operands)} "
                f"operand(s), expected 2 (address, mem_controller readback)")
        addr = node.operands[0]
        addr_res, z = node.results
        info = self.accessor_info[addr_res]
        aw, dw, seq = info["aw"], info["dw"], info["seq"]
        cap = info.get("cap", False)
        name = mem.unit_name("load", aw, dw, seq=seq, cap=cap)
        self.units.setdefault(name, mem.emit_unit("load", aw, dw, seq=seq, cap=cap))
        zr, za = self.oreq(z), self.oack(z)
        if "z_fork" in info:
            # The first accessor of a load-first port: its z is also the second accessor's program-order token
            # (see _resolve_mem_accessors).  The data is broadcast; the request is forked; the load sees the
            # C-element of both acknowledges.
            tok_req, tok_ack = info["z_fork"]
            zr, za = f"{inst}_zf_req", f"{inst}_zf_ack"
            self.emit(f"    wire {zr}, {za};")
            self.emit(f"    bd_fork #(.N(2)) {inst}_uztok (.rst(rst), .req({zr}), .ack({za}),")
            self.emit(f"        .req_out({{{tok_req}, {self.oreq(z)}}}), .ack_in({{{tok_ack}, {self.oack(z)}}}));")
        self.emit(f"    {name} {inst} (")
        self.emit(f"        .rst(rst),")
        if seq:
            self.emit(f"        .c_req({info['c_req']}), "
                      f".c_ack({info['c_ack']}),")
        self.emit(f"        .a_req({self.req(addr)}), .a_ack({self.ack(addr)}), "
                  f".a_data({self.data(addr)}),")
        self.emit(f"        .z_req({zr}), .z_ack({za}), "
                  f".z_data({self.odata_out(z)}),")
        self.emit(f"        .p_req({info['p_req']}), .p_ack({info['p_ack']}), "
                  f".p_addr({info['p_addr']}),")
        self.emit(f"        .p_wdata({info['p_wdata']}), .p_we({info['p_we']}), "
                  f".p_rdata({info['p_rdata']}));")

    def _op_store(self, node, inst):
        """A store: its own bdc_store_<AW>_<DW>[_seq] station.
        addressResult and dataResult are absorbed into the owning
        mem_controller and get no net.  z (the access completing) is
        control-only: if this store is the first accessor of a 2-way
        arbitrated chain, z becomes the SECOND accessor's program-order
        token (bdc/mem.py's own mechanism -- "a store's completion channel
        IS the next access's token", no new cell); with a single accessor
        nothing downstream needs to know a store finished, so z is tied off
        exactly as bd_snk would (cells/rtl/bd_end.v: assign ack = req).
        """
        if BDC_LINK_FASTFALL:
            raise EmitError("BDC_LINK_FASTFALL=1 is not audited for a kernel "
                            "with memory: bd_mem samples its request edges, "
                            "and a fast-falling request shortens the RAM "
                            "clock's low phase (rtl/bd_link.v RFAST)")
        if len(node.operands) != 2:
            raise EmitError(
                f"store at line {node.src_line} has {len(node.operands)} "
                f"operand(s), expected 2 (address, value)")
        addr, val = node.operands
        addr_res = node.results[0]
        # store_completion_rewrite's third result: z IS the completion
        # channel, into the block's completion join (see that function).
        done = node.results[2] if len(node.results) == 3 else None
        info = self.accessor_info[addr_res]
        aw, dw, seq = info["aw"], info["dw"], info["seq"]
        name = mem.unit_name("store", aw, dw, seq=seq)
        self.units.setdefault(name, mem.emit_unit("store", aw, dw, seq=seq))
        chained = "z_req_net" in info
        if chained and done is not None:
            raise EmitError(f"store at line {node.src_line}: chained and "
                            f"joined at once (_resolve_mem_accessors refuses "
                            f"this shape)")
        if done is not None:
            z_req_net, z_ack_net = self.oreq(done), self.oack(done)
        else:
            z_req_net = info["z_req_net"] if chained else f"{inst}_z_req"
            z_ack_net = info["z_ack_net"] if chained else f"{inst}_z_ack"
        if not chained and done is None:
            self.emit(f"    wire {z_req_net}, {z_ack_net};")
        self.emit(f"    {name} {inst} (")
        self.emit(f"        .rst(rst),")
        if seq:
            self.emit(f"        .c_req({info['c_req']}), "
                      f".c_ack({info['c_ack']}),")
        self.emit(f"        .a_req({self.req(addr)}), .a_ack({self.ack(addr)}), "
                  f".a_data({self.data(addr)}),")
        self.emit(f"        .d_req({self.req(val)}), .d_ack({self.ack(val)}), "
                  f".d_data({self.data(val)}),")
        self.emit(f"        .z_req({z_req_net}), .z_ack({z_ack_net}),")
        self.emit(f"        .p_req({info['p_req']}), .p_ack({info['p_ack']}), "
                  f".p_addr({info['p_addr']}),")
        self.emit(f"        .p_wdata({info['p_wdata']}), .p_we({info['p_we']}), "
                  f".p_rdata({info['p_rdata']}));")
        if not chained and done is None:
            self.emit(f"    assign {z_ack_net} = {z_req_net};")

    def _op_mem_controller(self, node, inst):
        """The shared memory port -- one bdc_memport[_arb]_<AW>_<DW>_<N> --
        wired to each accessor's own station (see _op_load/_op_store).
        Owns nothing else.

        memStart / ctrlEnd / memEnd: see the block comment inline below for
        what dynamatic's real mc_control FSM does and what this reproduces
        -- and where it deliberately stops rather than invent an unreviewed
        completion counter.
        """
        if BDC_LINK_FASTFALL:
            raise EmitError("BDC_LINK_FASTFALL=1 is not audited for a kernel "
                            "with memory: bd_mem samples its request edges, "
                            "and a fast-falling request shortens the RAM "
                            "clock's low phase (rtl/bd_link.v RFAST)")
        memend = node.results[-1]
        info = self.mc_info[memend]
        if info["inst"] != inst:
            raise EmitError(
                f"mem_controller at line {node.src_line}: instance name "
                f"{inst!r} disagrees with the pre-pass's {info['inst']!r} "
                f"-- instname() must be a pure function of (node, index)")
        aw, dw, n, arb = info["aw"], info["dw"], info["slots"], info["arb"]
        accessors = info["accessors"]

        # HOST_MEM: one more slot, the last, wired to the kernel's
        # <m>_host_* ports (see HOST_MEM at the top of this file).  The
        # kernel's own slots keep their numbers, so its stations, its wires
        # and its BD_SZ keys are exactly what they were.
        host = None
        if HOST_MEM:
            # On an arbitrated port (2 accessors) the host slot stands outside bd_arbiter (bdc/mem.py HOST ARB:
            # never live while a kernel slot is -- the bench's obligation, as on the plain port).
            host = host_base(self.func, info["memref"])
            self.host_wired.add(info["memref"])
        nport = n + (1 if host else 0)

        if arb and host:
            pname = f"bdc_memport_arb_host_{aw}_{dw}_{nport}"
            self.units.setdefault(pname, mem.emit_port(aw, dw, slots=nport, arb=True, host=True))
        else:
            pname = f"bdc_memport{'_arb' if arb else ''}_{aw}_{dw}_{nport}"
            self.units.setdefault(pname, mem.emit_port(aw, dw, slots=nport, arb=arb))

        # ONE PAIR OF DELAYS PER RAM -- mem.py's own header: each bd_mem in
        # a gang is placed and routed separately, so rule B and rule C
        # measure and propose a number per RAM, not per gang.  Keys match
        # verify/tighten.py's macro() convention (dots and underscores both
        # sanitise to '_'): BD_SZ_<UUT>_<INST>_UMEM<k>_USETUP/_UCO.
        nram = mem.ram_count(dw)
        parms = []
        for k in range(nram):
            dset = self.delay(f"{inst}_umem{k}_usetup", mem.DEFAULT_DSETUP)
            dco = self.delay(f"{inst}_umem{k}_uco", mem.DEFAULT_DCO)
            parms.append(f".DSETUP_{k}({dset})")
            parms.append(f".DCO_{k}({dco})")

        aw1, dw1 = max(aw, 1), max(dw, 1)
        for k in range(n):
            self.emit(f"    wire {inst}_s{k}_req, {inst}_s{k}_ack, "
                      f"{inst}_s{k}_we;")
            self.emit(f"    wire [{aw1 - 1}:0] {inst}_s{k}_addr;")
            self.emit(f"    wire [{dw1 - 1}:0] {inst}_s{k}_wdata;")
        self.emit(f"    wire [{dw1 - 1}:0] {inst}_rdata;")
        if arb and info.get("chained", True):
            # The token wire a chained store's z becomes -- see _op_store.
            # Declared here, not there: Verilog wires are order-free and
            # this is the one place that always runs for an arbitrated
            # controller regardless of which accessor happens to lower
            # first.
            self.emit(f"    wire {inst}_tok_req, {inst}_tok_ack;")

        def cat(sig):
            names = [f"{inst}_s{k}_{sig}" for k in range(n)]
            if host:
                names.append(f"{host}_{sig}")
            return names[0] if len(names) == 1 else "{" + ", ".join(reversed(names)) + "}"

        ack_port = f".s_ack({cat('ack')})" if arb else f".p_ack({inst}_s0_ack)"
        self.emit(f"    {pname} #({', '.join(parms)}) {inst}_uport (")
        self.emit(f"        .rst(rst),")
        self.emit(f"        .s_req({cat('req')}), .s_addr({cat('addr')}), "
                  f".s_wdata({cat('wdata')}),")
        self.emit(f"        .s_we({cat('we')}), {ack_port}, "
                  f".p_rdata({inst}_rdata));")
        if host and arb:
            # The arbitrated port hands the host slot its own acknowledge (s_ack[2], in cat('ack') above).
            self.emit(f"    assign {host}_rdata = {inst}_rdata;")
        elif host:
            # The plain port's acknowledge and read data are shared by every
            # slot; the kernel's stations gate them with their own `joined`,
            # so an idle station ignores a host access (bdc/mem.py: done).
            self.emit(f"    assign {host}_ack = {inst}_s0_ack;")
            self.emit(f"    assign {host}_rdata = {inst}_rdata;")

        # memStart / ctrlEnd / memEnd.
        #
        # dynamatic/data/verilog/support/mc_support.v's real mc_control FSM:
        # a 2-state IDLE/RUNNING machine.  memStart_valid moves IDLE ->
        # RUNNING.  ctrlEnd_valid latches "no more requests will come".
        # memEnd_valid = that latch AND allRequestsDone AND fsm_running;
        # memEnd_valid moves RUNNING -> IDLE (function_return) and clears
        # the latch.  For a LOAD-ONLY controller (dynamatic's own
        # mem_controller_storeless.v), allRequestsDone is HARDWIRED 1'b1 --
        # Dynamatic's own accepted simplification: loads are never tracked
        # for completion.  A controller with a STORE
        # (mem_controller_loadless.v) instead needs a real up/down counter,
        # remainingStores, incremented by each basic block's own ctrl count
        # token (the constant this pre-pass skips in the accessor group) and
        # decremented per completed store -- and ctrl_ready never
        # backpressures it, so promised counts can race ahead of actual
        # completions.
        #
        # This reproduces the load-only case with proven cells and nothing
        # new: a bd_link naturally captures memStart's one-shot pulse and
        # holds req_out high until its consumer's ack arrives -- exactly
        # "wait here until ctrlEnd shows up" -- then bd_join #(.N(2)) with
        # ctrlEnd produces memEnd.  Once both branches release, the link is
        # empty again, ready for the next invocation -- the same
        # IDLE-reset behaviour the real FSM has, and functionally identical
        # to mem_controller_storeless's own accepted limitation.
        #
        # For a store-having controller this same shortcut is correct only
        # because store_completion_rewrite has made ctrlEnd itself arrive
        # after every store of the call: each block's outgoing control token
        # (or, in the exit block, this controller's ctrlEnd) is joined with
        # the completions of that block's stores.  remainingStores == 0 is
        # then implied by ctrlEnd, by construction rather than by a counter
        # racing it.  The per-block store-count tokens carry nothing more
        # (their values were checked there) and are sunk here, so their
        # producers are not stalled.
        for k, c in enumerate(info.get("counts", ())):
            self.emit(f"    bd_snk #(.W({max(self.width(c), 1)})) {inst}_ucount{k} (")
            self.emit(f"        .req({self.req(c)}), .ack({self.ack(c)}), "
                      f".data({self.data(c)}));")

        memstart, ctrlend = info["memstart"], info["ctrlend"]
        hold = f"{inst}_started"
        d = self.delay(f"{inst}_uhold", 0)
        self.emit(f"    wire {hold}_req, {hold}_ack;")
        self.emit(f"    bd_link #(.W(1), .DELAY({d})) {inst}_uhold (")
        self.emit(f"        .rst(rst),")
        self.emit(f"        .req_in({self.req(memstart)}), "
                  f".ack_in({self.ack(memstart)}), .data_in(1'b0),")
        self.emit(f"        .req_out({hold}_req), .ack_out({hold}_ack), "
                  f".data_out());")
        self.emit(f"    bd_join #(.N(2)) {inst}_uend (")
        self.emit(f"        .rst(rst), "
                  f".req_in({{{self.req(ctrlend)}, {hold}_req}}),")
        self.emit(f"        .ack_out({{{self.ack(ctrlend)}, {hold}_ack}}),")
        self.emit(f"        .req({self.oreq(memend)}), "
                  f".ack({self.oack(memend)}));")

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

    # -- BDC_OP_FUSION: fused regions --------------------------------------

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
        self.emit(f"    // {chain}  fused by BDC_OP_FUSION "
                  f"(anchor line {anchor.src_line})")
        name, default = self._emit_fused_module(region, inst)
        d = self.delay(inst, default)
        z = anchor.results[0]
        if inst in SPEC_INC:
            ds = self.delay(inst + "_short", SPEC_INC[inst][1])
            self.emit(f"    {name} #(.DELAY({d}), .DELAY_SHORT({ds})) {inst} (")
        else:
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
        reqline = compute.request_delay("joined")
        extra_param = ""
        if inst in SPEC_INC:
            k, nshort = SPEC_INC[inst]
            if [nodes[i].op for i in region.node_ids] != ["addi"] or len(ext_w) != 1:
                raise EmitError(f"BDC_SPEC_INC={inst}: needs a single-op addi region with one external operand "
                                f"(got {chain}, {len(ext_w)} operands)")
            kk = k - 1
            extra_param = f", parameter DELAY_SHORT = {nshort}"
            reqline = (f"""wire z_long, z_short;
    bd_delay_gated #(.N(DELAY)) udly (.a(either), .gate(joined), .z(z_long));
    bd_delay_gated #(.N(DELAY_SHORT)) udly_s (.a(either), .gate(joined), .z(z_short));
    // speculative completion (BDC_SPEC_INC): long line only when x's low {k} bits are all ones (this carry runs
    // past bit {k}) or all zeros (the previous increment's carry is still discharging)
    wire spec_abort = (&e0_data[{kk}:0]) | ~(|e0_data[{kk}:0]);
    (* keep *) LUT3 #(.INIT(8'hE4)) uspec (.I0(spec_abort), .I1(z_short), .I2(z_long), .O(z_req));""")
        text = f"""
// Fused region: {chain}.  Generated by bdc/emit.py under BDC_OP_FUSION --
// do not edit.  One keep_hierarchy boundary, one bd_join, one matched delay
// for the whole region: see the BDC_OP_FUSION block comment above
// FUSABLE_OPS in bdc/emit.py for why this does not cost auditability.
`default_nettype none
(* keep_hierarchy *)
module {name} #(parameter DELAY = {default_total}{extra_param})
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
    {reqline}

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
            "shli", "shrsi", "shrui", "select") + tuple(sorted(compute.DIV)):
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
        if arg.ssa_name in e.memrefs:
            # A memref is not a channel -- see _resolve_widths().  Its
            # mem_controller instances get no top-level port; the memory
            # lives entirely inside the kernel, behind bd_mem.
            continue
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

    # ---- host memory ports (HOST_MEM; see its note at the top of this file) --
    # One set per memref argument, in signature order, after every channel, so
    # nothing a caller already connects by position moves.
    if HOST_MEM:
        taken = {portname(a.name) for a in func.args} | {portname(r.name) for r in func.results}
        for arg in func.args:
            if arg.ssa_name not in e.memrefs:
                continue
            aw, dw = e.memrefs[arg.ssa_name]
            b = host_base(func, arg.ssa_name)
            if b in taken:
                raise EmitError(f"--host-mem: the host port of memref {arg.name!r} would be named "
                                f"{b!r}, which is already a channel of @{func.name}")
            ports += [f"    input  wire             {b}_req",
                      f"    output wire             {b}_ack",
                      f"    input  wire [{aw - 1}:0]     {b}_addr",
                      f"    input  wire [{dw - 1}:0]     {b}_wdata",
                      f"    input  wire             {b}_we",
                      f"    output wire [{dw - 1}:0]     {b}_rdata"]
            if arg.ssa_name not in e.host_wired:
                # No mem_controller reads or writes this memref, so there is no
                # RAM behind its host port: complete every handshake at once and
                # read zero, which is what the kernel itself would see.
                e.emit(f"    // {arg.name}: no mem_controller uses this memref; its host port has no RAM.")
                e.emit(f"    assign {b}_ack = {b}_req;")
                e.emit(f"    assign {b}_rdata = {dw}'b0;")

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
                f"--probe names {name!r}, but BDC_OP_FUSION folded that "
                f"channel into a fused cell -- there is no net left to tap. "
                f"Probe an external input or the region's own output instead.")
        if ssa in e.mem_absorbed:
            raise EmitError(
                f"--probe names {name!r}, but that channel is a load/store's "
                f"address or data round trip with its own mem_controller, "
                f"absorbed entirely inside a bdc_load/bdc_store station -- "
                f"there is no net left to tap. Probe the load's dataResult "
                f"or the accessor's own operand instead.")
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
            # Absorbed by BDC_OP_FUSION: an eliminated (source, constant)
            # pair, or a fused region member other than its anchor.  Nothing
            # drives or reads these nets any more, so they are not declared
            # at all rather than left as unused wires -- the "DECLARATIONS
            # FIRST" note below is about ordering what IS referenced, and a
            # declaration for a name nothing references invites exactly the
            # confusion that note is guarding against.
            continue
        if ssa in e.mem_absorbed:
            # A load's addressResult, a store's addressResult/dataResult, or
            # a mem_controller's own data-output result -- the station's
            # internal p_addr/p_rdata round trip.  See _resolve_mem_accessors:
            # no net exists for these, by design, so none is declared.
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
        if not arg.ssa_name or arg.ssa_name in e.memrefs:
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
    # A memref argument is not a channel and gets no top-level port on
    # bdc_<func> (see emit_func's ports/bridge loops and _resolve_widths) --
    # so this top, which drives every argument from its own spine, must skip
    # it too or the instantiation below names a port that does not exist.
    real_args = [a for a in func.args if not a.raw.startswith("memref")]
    inputs = [portname(a.name) for a in real_args]
    outputs = [portname(r.name) for r in func.results]
    total = sum(a.width for a in real_args)
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
    for i, arg in enumerate(real_args):
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
    if HOST_MEM:
        # The host ports are idle here: this top never fills a memory.
        for a in func.args:
            m = re.fullmatch(r"memref<(\d+)x[iu](\d+)>", a.raw) if a.raw.startswith("memref") else None
            if m:
                b = host_base(func, a.ssa_name)
                aw = max(1, (int(m.group(1)) - 1).bit_length())
                conns.append(f"        .{b}_req(1'b0), .{b}_addr({aw}'b0), "
                             f".{b}_wdata({m.group(2)}'b0), .{b}_we(1'b0),")
    conns[-1] = conns[-1].rstrip(",")

    decls = []
    for a in real_args:
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
// The spine's own ack-fall hold (bd_link.v DACK), sized by rule H like any
// other -- its data is constant, but the audit cannot know that.
`ifndef BD_SZ_UPIPE_UACK
 `define BD_SZ_UPIPE_UACK {ACK_PAD}
`endif
// ... and its stage-to-stage request pad (bd_link.v SDELAY), sized by rule I.
`ifndef BD_SZ_UPIPE_SDELAY
 `define BD_SZ_UPIPE_SDELAY {STAGE_PAD}
`endif

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

    bd_pipe #(.W({nb}), .N(4), .SDELAY(`BD_SZ_UPIPE_SDELAY),
              .DACK(`BD_SZ_UPIPE_UACK)) upipe (
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


# BDC_LINK_RST=1 (opt-in, research/data/suite/hangs.md; unset, the output is byte-identical): every link's data latch is
# defined at reset.  bd_link's latch (bd_latch) has no reset, so it powers up at whatever value the die gives it and the
# gate starts it at X; a value read before the first token has passed is then undefined (the automatic ipow seed-4
# route's first call: an exit test read X from the e >> 1 latches and the X stayed in the C-elements).  The reset value
# is a polarity, not a new primitive (CLAUDE.md): bd_latch_rst with RESET_VALUE 0, in a link composed here from the
# same frozen cells and instance names as bd_link (bd_link_ctl ctl, bd_delay rdly / uack) so every matched delay and
# every rule's chain keeps its name.  Cost: one LUT per latch bit instead of one per two (bd_latch packs a pair).
LINK_RST = os.environ.get("BDC_LINK_RST", "0") == "1"
LINK_RST_UNITS = """
module bdc_link_rst #(parameter W = 8, parameter integer DELAY = 0, parameter integer DACK = 0,
                      parameter BROAD = 1, parameter integer LDN = 0, parameter RFAST = 0)
    (input  wire             rst,
     input  wire             req_in,
     output wire             ack_in,
     input  wire [W-1:0]     data_in,
     output wire             req_out,
     input  wire             ack_out,
     output wire [W-1:0]     data_out);
    wire c;
    bd_link_ctl ctl (.req_in(req_in), .c_next(ack_out), .rst(rst), .c(c));
    bd_latch_rst #(.W(W), .RESET_VALUE(64'd0)) lat (.d(data_in), .en(c), .rst(rst), .q(data_out));
    bd_delay #(.N(DELAY), .FASTFALL(RFAST)) rdly (.a(c), .z(req_out));
    bd_delay #(.N(DACK), .FASTRISE(1)) uack (.a(c), .z(ack_in));
endmodule

module bdc_pipe_rst #(parameter W = 8, parameter N = 2, parameter integer DELAY = 0,
                      parameter integer SDELAY = 1, parameter integer DACK = 0, parameter BROAD = 1)
    (input  wire             rst,
     input  wire             req_in,
     output wire             ack_in,
     input  wire [W-1:0]     data_in,
     output wire             req_out,
     input  wire             ack_out,
     output wire [W-1:0]     data_out);
    genvar i;
    generate
    if (N == 1) begin : one
        bdc_link_rst #(.W(W), .DELAY(DELAY), .DACK(DACK), .BROAD(BROAD)) u (
            .rst(rst), .req_in(req_in), .ack_in(ack_in), .data_in(data_in),
            .req_out(req_out), .ack_out(ack_out), .data_out(data_out));
    end else begin : many
        wire [N:0] r, a;
        wire [W*(N+1)-1:0] dat;
        assign r[0] = req_in;
        assign ack_in = a[0];
        assign a[N] = ack_out;
        assign req_out = r[N];
        assign dat[W-1:0] = data_in;
        assign data_out = dat[W*N +: W];
        for (i = 0; i < N; i = i + 1) begin : stage
            bdc_link_rst #(.W(W), .DELAY(i + 1 == N ? DELAY : SDELAY),
                           .DACK(DACK), .BROAD(i + 1 == N ? BROAD : 0)) u (
                .rst(rst),
                .req_in(r[i]), .ack_in(a[i]), .data_in(dat[W*i +: W]),
                .req_out(r[i+1]), .ack_out(a[i+1]),
                .data_out(dat[W*(i+1) +: W]));
        end
    end
    endgenerate
endmodule
"""


def _link_rst(text):
    """BDC_LINK_RST: every bd_link / bd_pipe instance becomes its reset-latch twin."""
    for m in re.finditer(r"\bbd_(?:link|pipe) #\(\.W\((\d+)\)", text):
        if int(m.group(1)) > 64:
            raise EmitError(f"BDC_LINK_RST: a {m.group(1)}-bit link (bd_latch_rst's RESET_VALUE holds 64 bits)")
    text = re.sub(r"\bbd_link #\(", "bdc_link_rst #(", text)
    return re.sub(r"\bbd_pipe #\(", "bdc_pipe_rst #(", text)


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
    if LINK_RST:
        units = {k: _link_rst(v) for k, v in units.items()}
        units["bdc_link_rst"] = LINK_RST_UNITS
        body = _link_rst(body)
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
    ap.add_argument("--host-mem", action="store_true",
                    help="give every memory a host port: one more one-hot slot "
                         "on its bdc_memport, wired to <memref>_host_* kernel "
                         "ports (a no-op for a kernel without memref "
                         "arguments); also settable as BDC_HOST_MEM=1")
    args = ap.parse_args()

    if args.probe:
        PROBE[:] = [p for p in args.probe.split(",") if p]
    if args.host_mem:
        global HOST_MEM
        HOST_MEM = True

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
