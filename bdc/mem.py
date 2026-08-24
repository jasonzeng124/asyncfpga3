#!/usr/bin/env python3
"""Stage 6 groundwork: one memory ACCESS, as a bundled-data cell.

THE RESULT THIS FILE EXISTS TO RECORD

A load is a compute unit whose function is the RAM.  Not "like" one -- the
same wiring, arc for arc.  bdc/compute.py builds every arithmetic cell as

    bd_join over the operands  ->  joined ;  every operand's ack = z_ack
    z_req  = delta(joined)                    <- bd_delay, sized post-route
    z_data = f(operand data)                  <- combinational

and bd_mem is already exactly that shape with the delay inside it:

    bd_mem.req  = joined         <- see THE PORT CLAIM below; it is really
                                    `joined & ~done`, which is the same edge
    bd_mem.ack  = z_req          <- DSETUP + the explicit clock buffer + DCO
    bd_mem.rdata = z_data        <- the RAM, clocked by the request itself

So a single-port access needs NO new controller, and that is worth stating
because the obvious first draft is a hand-built four-phase sequencer with a
capture latch, a done C-element and a return-to-zero detector.  None of it is
needed.  Substituting bd_mem for the bd_delay is the whole cell.

THE RETURN TO ZERO IS THE ONE THING THAT IS NOT FREE, AND IT COSTS ONE GATE

bd_mem's header names "pipelined return-to-zero overlap" as a failure this
cell owns: back-to-back accesses whose reset phases overlap corrupt the port,
and it records that history of being misdiagnosed as a margin problem and
"fixed" by scaling guard delays, which never worked because the mechanism is
sequencing.  So it is worth being exact about where the sequencing comes from.

The first version of this file claimed it fell out of bd_join for free.  It
does not, and the reason is worth writing down because the claim is plausible:

    bd_join #(.N(n)) u (..., .req_in(...), .ack_out(...), .req(q), .ack(z_ack));
    bd_ctree #(.N(N)) u (.a(req_in), .rst(rst), .q(req));
    assign ack_out = {N{ack}};

`joined` is a C-element over the INPUT REQUESTS ONLY.  It has no path from
z_ack at all.  So the sequence really runs

    p_ack rises      DSETUP + buffer + DCO after the request
    z_ack rises      the consumer took the value
    a_req falls      the producer saw its ack
    joined falls  -> p_req falls, and z_req falls with it
    a_ack falls      one arc later, because a_ack IS z_ack   (*)

(*) as of THE PORT CLAIM below, p_req falls earlier than this -- at p_ack, not
at joined.  The rest of the trace is unchanged and so is the conclusion.

and the producer is free to present the next address HERE -- while ram_clk is
still high, DSETUP + DCO before p_ack falls.  The next request would then find
the manufactured clock already high, there would be no second rising edge, and
the second access would silently not happen.  That is exactly the failure
bd_mem warns about, reached by the shortest possible route.

The fix is one gate and it is not a delay.  The operands must be released when
the PORT is quiet, not when the consumer is done, so the acknowledge sent back
to them is held up until p_ack falls:

    hold = ~rst & (z_ack | (hold & p_ack))

An asymmetric C-element: it rises on z_ack alone, so the producer is told
promptly that its value was taken, and it falls only when z_ack and p_ack are
both low, so the producer cannot present the next address until the port has
finished resetting.  One LUT6, the same cost as every other C-element in the
library, and it differs from bd_c2's INIT in exactly one bit -- 0x00EA against
0x00E8 -- which is the bit that makes the rise asymmetric.

With that, serialisation is correct by construction rather than by margin, and
it composes: an operand released only at port-quiet is exactly the release
signal a program-order token chain needs, so the token costs nothing extra.

Be precise about WHICH signal, because the obvious cheaper one does not work.
The token must wait for a_ack to FALL, not for p_ack to fall.  p_ack is
shared, and a_ack lags it on every path -- z_req rises with p_ack, the
consumer only then drops z_ack, and hold needs z_ack and p_ack both low.  Releasing on p_ack lets the producer offer its next operand into an
acknowledge that never fell.  cells/tb/tb_bdc_memseq.v measures this: the p_ack
rule fails identically at every consumer speed from 0 ps to 32 hops, which is
what tells you it is structural and not a race.  See bdc/AUDIT.md section 7.

AND DCO IS THE ADDRESS HOLD GUARD, NOT ONLY THE CLOCK-TO-OUT LINE

Falling out of the same trace: the address is released when the port claim is,
which is DSETUP + DCO after the RAM captured it -- the capture edge is DSETUP
after the request and the claim drops at the acknowledge, DCO later.  So DCO is
what provides the hold window, and rule C sizes it for clock-to-out alone.

(`done` shortened this.  The claim used to persist until the operands were
withdrawn, so the measured hold was whatever the dataflow happened to take;
now it is bounded by the RAM's own round trip and by nothing else, which is
the point -- it is a number the port controls.  tb_bdc_mem.v measures 2700 ps
for both address and data where it read 2632 / 2756 before.  Shortening a
matched delay is the direction simulation cannot check, so note that DCO
itself did not change: what went away was slack that was never guaranteed.)

This paragraph used to say prjxray's model checks setup and says nothing about
hold.  That was wrong: BRAM_L.sdf carries HOLD arcs right next to the SETUP
ones it was already being read for, e.g.

    (HOLD ADDRAU (posedge CLKARDCLKU) (-0.566::0.360))

They are exported by sim/bd_prims_sim.v now.  verify/tighten.py reports the
bound (2x its own clock-to-out number, since DCO appears twice in the release
path), and tb_bdc_mem.v measures the real value: 2700 ps against 360 needed.
That makes shortening DCO risky in two independent ways at once, and
shortening a matched delay is already the direction simulation cannot see.

THE PORT CLAIM MUST RETURN TO ZERO ON ITS OWN, AND THAT IS WHAT `done` IS

Everything above is about ONE station's accesses.  The moment two stations
share the port -- which is the entire point of a port -- `p_req = joined` is a
deadlock, and it is worth being exact because it also looks free.

`joined` is high for as long as the OPERANDS are held, and the operands are
held until the consumer is finished.  If that consumer is a later access on
the same memory, the second station cannot get the port until the first
releases it, and the first cannot release it until the second finishes.  An
arbiter does not help: neither request is illegal, so there is nothing for it
to reject.  Measured, with bd_arbiter in place: ONE RAM edge, then nothing.

The port claim therefore has to complete and let go by itself, on the RAM's
schedule rather than the dataflow's:

    done  = joined & (p_ack | done)      one LUT, gated by joined on BOTH
                                         terms so an idle station reads zero
                                         even while a shared p_ack is high
    p_req = joined & ~done               dropped the moment the RAM answered
    z_req = done                         the result, held until the operands go

Two LUTs.  `done` is the old `p_ack & joined` latched, so z_req is a rename --
and a necessary one, because p_ack now falls long before the consumer has
taken the result and z_req has to outlast it.

What this buys is that the port sees one clean four-phase transaction per
access, bounded by the RAM, with nothing of the surrounding dataflow inside
it.  That is the property a shared resource needs, and it is the difference
between "the caller must guarantee one-hotness" and "the port arbitrates".

THE PORT AND THE STATION ARE SEPARATE MODULES, AND THAT IS NOT TIDINESS

The first draft had each unit own its own bd_mem.  It is not testable.  A RAM
powers up at zero and bd_mem has no INIT parameter, so a load-only design
reads a memory nothing ever wrote -- and a store unit with its own RAM writes
one nothing ever reads.  Proving a load returns what a store put there needs
both on ONE port, which means the port is a module and the accesses are
modules that drive it.

So `bdc_memport_<AW>_<DW>_<N>` owns the RAM gang and multiplexes N slots, and
`bdc_load_*` / `bdc_store_*` are stations that drive a slot.  The mux is
one-hot AND-OR over the slot requests, which is correct ONLY while at most one
slot's request is high -- an obligation on whoever wires them up, checked in
simulation by the port module itself rather than assumed.

WHO GUARANTEES THE ONE-HOTNESS: EITHER THE CALLER OR bd_arbiter

There are two ports, and the difference is exactly that obligation.

`bdc_memport_*` is the plain one: one shared acknowledge, mux selected by the
slot requests, and the caller must not let two slots request at once.  A
caller that sequences the slots itself (cells/tb/tb_bdc_mem.v does) is using
it as intended.

`bdc_memport_arb_*` puts bd_arbiter between the slots and the RAM.  The slots
become r1/r2, the RAM gang becomes R0/A0, and the mux selects are g1/g2, which
are exclusive BY CONSTRUCTION -- so the obligation becomes a guarantee and
each slot gets its own acknowledge, A1/A2, instead of a shared one.  It is
two slots only; a tree for more is not built and the generator refuses rather
than guessing one.

Program order on top of that is `:seq`, a station variant with one more join
input: a token channel `c`.  It gates nothing -- it is simply another operand
that must arrive -- and it is acknowledged by the same `hold` the operands
are, so it is released at port-quiet, which is the release rule this file
argues for above.  The chain is then ordinary channel composition: a store's
completion channel IS the next access's token, `store.z -> load.c`.  No
sequencer, no new cell.

The arbiter is not optional there.  With the plain port the token chain gets
the DATA right and the PROTOCOL wrong -- 12 exclusivity violations and 12 RAM
edges for 24 accesses, the load reading correctly only because bd_mem sets
WRITE_MODE_A("WRITE_FIRST") and handed back the data being written.  With the
arbiter and `done` it is 24 edges for 24 accesses and zero violations, which
is also what rules out the passthrough: a WRITE_FIRST read is the same edge as
its write, and these are two.  bdc/AUDIT.md section 7 has the measurements.

THE WIDE PORT IS A GANG, NOT A WIDER RAM

bd_mem is frozen at one RAMB18E1 in x18 mode, so DIADI/DOADO are sixteen bits
and DW > 16 does not elaborate into a wider RAM -- it silently truncates.  A
32-bit memref is therefore two bd_mem instances side by side sharing one
request, with their acknowledges joined by a C-tree: all of them have answered
before z_req rises, all of them have reset before it falls.  The C-tree sits
AFTER each DCO, which lengthens the acknowledge -- the safe direction for a
clock-to-out line, and the direction rule C's margin then understates rather
than overstates.

THE DELAY KEYS

Two matched delays per RAM, both inside bd_mem: `usetup` and `uco`.
verify/tighten.py names its answer after the routed instance path
(macro('umem.usetup') -> BD_SZ_UMEM_USETUP), so a unit instantiated as
`uload3` inside `uut` produces paths `uut.uload3.umem0.usetup` and the key
BD_SZ_UUT_ULOAD3_UMEM0_USETUP.  bdc/emit.py registers one pseudo-instance per
delay under exactly those names; get that wrong and the tightening loop
reports success having changed nothing, which bdc/compute.py's header records
being reached twice by different routes.
"""

import math
import os

# BDC_MEM_NAIVE_ACK=1 emits the station WITHOUT the asymmetric C-element --
# operand acknowledges tied straight to z_ack, which is what bd_join would do.
# It exists so the negative control is a switch rather than a hand edit: a
# check that has never been seen to fail is not evidence.  cells/tb/tb_bdc_mem.v
# records what it produces.  Never set it for anything that will be built.
NAIVE_ACK = os.environ.get("BDC_MEM_NAIVE_ACK") == "1"

# One RAMB18E1 in x18 mode: 1024 words of 16 data bits (plus 2 parity, unused).
RAM_WORDS = 1024
RAM_DW = 16

# Placeholders only.  bd_mem's own header says the same thing about its
# defaults: post-route sizing replaces both, and tb_mem derives them from
# prjxray's BRAM_L.sdf rather than from a constant typed into a source file.
DEFAULT_DSETUP = 8
DEFAULT_DCO = 12


class MemError(Exception):
    pass


def unit_name(kind, aw, dw, seq=False):
    if kind not in ("load", "store"):
        raise MemError(f"no memory unit for {kind!r} -- load or store")
    return f"bdc_{kind}{'_seq' if seq else ''}_{aw}_{dw}"


def ram_count(dw):
    """How many bd_mem instances one word of `dw` bits needs."""
    return (dw + RAM_DW - 1) // RAM_DW


def check(aw, dw):
    """Refuse anything the frozen cell cannot actually hold.

    AW is checked against the RAM's own depth rather than against bd_mem's
    parameter, because bd_mem does not check it: `a14 = {addr, 4'b0000}` at
    AW = 11 is a 15-bit value assigned to a 14-bit wire, which Verilog
    truncates from the TOP.  Address bit 10 disappears and every access folds
    onto the low half of the RAM -- silently, and with the write path folded
    the same way, so a store-then-load test still passes.
    """
    if aw < 1:
        raise MemError(f"address width {aw} is not a width")
    if (1 << aw) > RAM_WORDS:
        raise MemError(
            f"address width {aw} asks for {1 << aw} words; one bd_mem is "
            f"{RAM_WORDS} (RAMB18E1, x18).  bd_mem is frozen and does not "
            f"check this -- it would truncate the top address bit and fold "
            f"the memory in half without failing.  Split the memref or widen "
            f"the cell, do not pass this through")
    if dw < 1:
        raise MemError(f"data width {dw} is not a width")


def emit_unit(kind, aw, dw, seq=False):
    """One memory access STATION as a self-contained Verilog module.

    `seq` adds a control channel `c` carrying a PROGRAM-ORDER TOKEN.  It costs
    one more input to the existing join and nothing else, because the release
    rule a token chain needs is the one this station already implements -- see
    the `c` channel comment in the emitted module, and bdc/AUDIT.md section 7
    for why a_ack rather than p_ack is the only correct release point.

    It owns no RAM.  It drives one slot of a bdc_memport and is otherwise the
    same shape as an arithmetic unit from bdc/compute.py: join the operands,
    hand them to the boundary, and let the boundary's own acknowledge be this
    cell's outgoing request.
    """
    check(aw, dw)
    name = unit_name(kind, aw, dw, seq)
    store = kind == "store"

    # Input channels.  A load consumes the address; a store consumes the
    # address and the value.  Both are a JOIN: the RAM boundary means nothing
    # until every operand has arrived, exactly as for an arithmetic unit.
    chans = (["c"] if seq else []) + ["a"] + (["d"] if store else [])
    cw = {"a": aw, "d": dw}

    decls = []
    for c in chans:
        if c == "c":
            # The program-order token.  A CONTROL channel: it carries no data,
            # only the right to proceed, so it gets no data net -- the same
            # convention a store's result follows below.
            #
            # It joins the operands rather than gating them, which is the
            # whole point: `joined` already means "everything this access
            # needs has arrived", and the token is one more thing it needs.
            # And the acknowledge it gets is `hold`, shared with the operands,
            # so the token is released exactly when the operands are -- which
            # bdc/AUDIT.md section 7 establishes is the ONLY correct release
            # point.  Releasing on p_ack instead fails at every consumer
            # speed; cells/tb/tb_bdc_memseq.v measures it.
            decls += [f"     input  wire             {c}_req,",
                      f"     output wire             {c}_ack,"]
            continue
        pad = " " * max(0, 7 - len(str(cw[c] - 1)))
        decls += [f"     input  wire             {c}_req,",
                  f"     output wire             {c}_ack,",
                  f"     input  wire [{cw[c] - 1}:0]{pad}{c}_data,"]

    req_cat = "{" + ", ".join(f"{c}_req" for c in reversed(chans)) + "}"
    ack_cat = "{" + ", ".join(f"{c}_ack" for c in reversed(chans)) + "}"

    dpad = " " * max(0, 7 - len(str(dw - 1)))
    apad = " " * max(0, 7 - len(str(aw - 1)))

    if NAIVE_ACK:
        hold_block = "\n".join([
            "    // BDC_MEM_NAIVE_ACK -- THE NEGATIVE CONTROL, AND IT IS WRONG.",
            "    // The operand acknowledges are tied straight to z_ack, which is",
            "    // what bd_join does.  cells/tb/tb_bdc_mem.v records what happens.",
            f"    assign {ack_cat} = {{{len(chans)}{{z_ack}}}};"])
    else:
        hold_block = "\n".join([
            "    wire hold;",
            "    (* keep *) LUT6 #(.INIT(64'h00EA_00EA_00EA_00EA)) uhold (",
            "        .I0(z_ack), .I1(p_ack), .I2(hold), .I3(rst), .I4(1'b0), .I5(1'b0),",
            "        .O(hold));",
            f"    assign {ack_cat} = {{{len(chans)}{{hold}}}};"])
    # A store's result is the ACCESS COMPLETING, which carries no value.  It is
    # a control channel and gets no data net, matching the convention every
    # other cell here follows.
    zdecl = ([] if store else
             [f"     output wire [{dw - 1}:0]{dpad}z_data,"])

    return f"""
// {kind} station, {aw}-bit address, {dw}-bit word.  Generated by bdc/mem.py -- do not edit.
//
// Drives ONE slot of a bdc_memport.  It carries no matched delay of its own:
// the delay this access depends on is bd_mem's DSETUP and DCO, inside the port
// module, audited there by verify/tighten.py rules B and C.  There is
// deliberately no `uor` instance here -- that is how rule A finds a request
// boundary to audit, and this cell does not have one.
`default_nettype none
(* keep_hierarchy *)
module {name}
    (input  wire             rst,
{chr(10).join(decls)}
     output wire             z_req,
     input  wire             z_ack,
{chr(10).join(zdecl) + chr(10) if zdecl else ""}     // The port slot.  p_req is this station's claim on the RAM; the port
     // module ORs it with the other slots' and muxes the payload by it.
     output wire             p_req,
     input  wire             p_ack,
     output wire [{aw - 1}:0]{apad}p_addr,
     output wire [{dw - 1}:0]{dpad}p_wdata,
     output wire             p_we,
     input  wire [{dw - 1}:0]{dpad}p_rdata);

    // Every operand must have arrived before the RAM boundary means anything.
    // This is bd_join's C-tree without bd_join's acknowledge: `joined` is a
    // C-element over the input requests, which is what is wanted, but
    // ack_out = {{N{{z_ack}}}} is NOT -- see bdc/mem.py's header for the trace.
    wire joined;
    bd_ctree #(.N({len(chans)})) ujoin (.a({req_cat}), .rst(rst), .q(joined));

    // The operands are released when the PORT is quiet, not when the consumer
    // is done.  Asymmetric C-element: rises on z_ack alone so the producer
    // learns promptly that its value was taken; falls only when z_ack and
    // p_ack are both low, so the next address cannot arrive while the
    // manufactured clock is still high.  Without this the second access
    // silently does not happen -- there is no second rising edge for it.
    //
    // 0x00EA is bd_c2's 0x00E8 with one bit changed: the code where a alone
    // is high.  That bit is the asymmetry, and it is the whole cell.
{hold_block}

    // THE PORT CLAIM RETURNS TO ZERO ON ITS OWN, which is what makes the port
    // shareable.  `p_req = joined` was the obvious thing and it deadlocks: it
    // holds the port for as long as the OPERANDS are held, and the operands
    // are held until the consumer -- possibly a later access on the same
    // memory -- is finished.  Two stations chained in program order then wait
    // on each other forever, and the arbiter cannot break it because there is
    // nothing wrong with either request.  Measured: one RAM edge, then
    // nothing (tb_bdc_memseq -DBDC_SEQ_TOKEN before this cell existed).
    //
    // `done` is the access having happened, remembered until the operands go
    // away.  It is gated by `joined` on BOTH terms so an idle station reads
    // zero even while some other slot's acknowledge is high -- that matters on
    // the unarbitrated port, where p_ack is shared.
    //
    //     done  = joined & (p_ack | done)      LUT3, I0 p_ack, I1 joined,
    //                                          I2 done, I3 rst clears
    //     p_req = joined & ~done               the claim, dropped on completion
    //
    // So the port sees one clean four-phase transaction per access and is free
    // again the moment the RAM answered, whatever the station's operands are
    // still waiting for downstream.
    wire done;
    (* keep *) LUT6 #(.INIT(64'h00C8_00C8_00C8_00C8)) udone (
        .I0(p_ack), .I1(joined), .I2(done), .I3(rst), .I4(1'b0), .I5(1'b0),
        .O(done));
    (* keep *) LUT2 #(.INIT(4'h2)) upr (.I0(joined), .I1(done), .O(p_req));

    assign p_addr  = a_data;
    assign p_wdata = {"d_data" if store else f"{dw}'b0"};
    assign p_we    = 1'b{1 if store else 0};

    // The port's acknowledge IS this cell's outgoing request.  That is the
    // whole substitution this file is about: bd_mem's DSETUP + buffer + DCO
    // stands exactly where bdc/compute.py puts its bd_delay.
    //
    // It used to be `p_ack & joined`, gated because p_ack is shared.  `done`
    // is that same conjunction LATCHED, so this is now just a rename -- and a
    // necessary one: p_ack falls as soon as the claim is released, which is
    // long before the consumer has taken the result.  z_req must outlast it.
    // z_req therefore rises when the RAM answered and falls when the operands
    // are withdrawn, which is after its own acknowledge.
    assign z_req = done;
{"" if store else "    assign z_data  = p_rdata;"}
endmodule
`default_nettype wire
"""


def emit_port(aw, dw, slots=1, arb=False):
    """The RAM gang and its slot mux, as a self-contained Verilog module.

    `arb` puts a bd_arbiter in front of the RAM instead of trusting the caller
    to keep the slot requests one-hot.  That changes the interface: each slot
    gets its OWN acknowledge (`s_ack`), because that is what an arbiter hands
    back, and the payload mux selects on the arbiter's GRANTS, which are
    exclusive by construction rather than by obligation.
    """
    check(aw, dw)
    n = ram_count(dw)
    if arb and slots != 2:
        raise MemError(
            f"arbitrated port asked for {slots} slots; only 2 is implemented. "
            f"bd_arbiter arbitrates two requesters, so N slots need a TREE of "
            f"them with each leaf's select ANDed down its path to the root. "
            f"That is not written yet, and guessing it would put an unproven "
            f"mutual-exclusion argument under a RAM")
    name = f"bdc_memport{'_arb' if arb else ''}_{aw}_{dw}_{slots}"
    sel = (lambda k: f"g{k + 1}") if arb else (lambda k: f"s_req[{k}]")

    dpad = " " * max(0, 7 - len(str(dw - 1)))
    apad = " " * max(0, 7 - len(str(aw - 1)))

    # ONE PAIR OF DELAYS PER RAM, not one pair for the gang.  Each bd_mem in a
    # gang is placed and routed separately, so rule B and rule C measure each
    # one's setup and clock-to-out against its OWN clock path and propose two
    # different numbers.  A shared parameter would silently collapse those into
    # whichever was written last -- and sizing is per-delay-element here, never
    # global.  The names line up with verify/tighten.py's macro convention:
    # macro('uport.umem1.usetup') -> BD_SZ_UPORT_UMEM1_USETUP, passed in at the
    # instance as .DSETUP_1(...).
    parlist = ",\n                ".join(
        f"parameter DSETUP_{k} = {DEFAULT_DSETUP}, parameter DCO_{k} = {DEFAULT_DCO}"
        for k in range(n))

    # One-hot AND-OR mux.  At most one slot's request is high, so an OR of
    # masked payloads is the whole selector -- no priority, no encoder, and
    # nothing that changes value while a request is high, because the slot
    # holding the request is the only one contributing.
    mux = []
    for sig, w in (("addr", aw), ("wdata", dw)):
        terms = " |\n                    ".join(
            f"({{{w}{{{sel(k)}}}}} & s_{sig}[{w}*{k} +: {w}])"
            for k in range(slots))
        mux.append(f"    wire [{w - 1}:0] m_{sig} = {terms};")
    weterms = " | ".join(f"({sel(k)} & s_we[{k}])" for k in range(slots))
    mux.append(f"    wire m_we = {weterms};")

    rams = []
    for i in range(n):
        lo = i * RAM_DW
        hi = min(dw, lo + RAM_DW) - lo
        wd = (f"m_wdata[{lo + hi - 1}:{lo}]" if hi == RAM_DW
              else f"{{{RAM_DW - hi}'b0, m_wdata[{lo + hi - 1}:{lo}]}}")
        if hi == RAM_DW:
            rd = f"p_rdata[{lo + hi - 1}:{lo}]"
        else:
            rams.append(f"    wire [{RAM_DW - hi - 1}:0] rd_hi{i};")
            rd = f"{{rd_hi{i}, p_rdata[{lo + hi - 1}:{lo}]}}"
        rams += [
            f"    bd_mem #(.AW({aw}), .DW({RAM_DW}),",
            f"             .DSETUP(DSETUP_{i}), .DCO(DCO_{i}), .USE_BUFG(0)) umem{i} (",
            f"        .req(m_req), .ack(ram_ack[{i}]),",
            f"        .addr(m_addr), .wdata({wd}), .we(m_we),",
            f"        .rdata({rd}));",
        ]

    gack = "m_ack" if arb else "p_ack"
    if n == 1:
        joinacks = f"    assign {gack} = ram_ack[0];"
    else:
        joinacks = (
            "    // Every word has answered before the acknowledge rises, and\n"
            "    // every word has reset before it falls.  A C-tree is the only\n"
            "    // gate that means both.  It sits AFTER each DCO, which\n"
            "    // lengthens the acknowledge -- the safe direction, and the\n"
            "    // direction rule C's margin then understates.\n"
            f"    bd_ctree #(.N({n})) uackj (.a(ram_ack), .rst(rst), .q({gack}));")

    words = f"{n} x {RAM_DW} bits" if n > 1 else f"{RAM_DW} bits"

    if arb:
        excl_note = (
            "// EXCLUSIVITY IS THIS MODULE'S JOB, NOT THE CALLER'S.  bd_arbiter\n"
            "// takes both slot requests, hands the RAM a single request, and\n"
            "// returns a separate acknowledge per slot.  Its g1/g2 grants are\n"
            "// exclusive by construction, so the AND-OR mux below selects on\n"
            "// THOSE and not on the raw requests.\n"
            "//\n"
            "// The unarbitrated bdc_memport puts this obligation on its caller,\n"
            "// and cells/tb/tb_bdc_memseq.v measures what happens when a plain\n"
            "// program-order token chain is asked to discharge it: correct data,\n"
            "// correct four-phase, and half the accesses silently not happening,\n"
            "// because a station raises its completion while it still holds the\n"
            "// port.  See bdc/AUDIT.md section 7.")
        ackport = ("     output wire [%d:0]%ss_ack,\n"
                   % (slots - 1, " " * max(0, 7 - len(str(slots - 1)))))
        reqblock = "\n".join([
            "    wire m_req, m_ack, g1, g2;",
            "    bd_arbiter uarb (",
            "        .rst(rst),",
            "        .r1(s_req[0]), .A1(s_ack[0]),",
            "        .r2(s_req[1]), .A2(s_ack[1]),",
            "        .R0(m_req), .A0(m_ack), .g1(g1), .g2(g2));"])
    else:
        excl_note = (
            "// AT MOST ONE SLOT REQUEST MAY BE HIGH AT A TIME.  The mux below is\n"
            "// a one-hot AND-OR and says nothing useful about two live slots;\n"
            "// worse, two live slots mean the RAM's manufactured clock never\n"
            "// falls between them, so there is no second edge and the second\n"
            "// access silently does not happen.  Enforcing that is the caller's\n"
            "// job -- and cells/tb/tb_bdc_memseq.v shows a program-order token\n"
            "// chain does NOT enforce it.  Use the arbitrated variant unless the\n"
            "// caller can prove exclusivity some other way.  This module checks\n"
            "// it in simulation so a wiring mistake is a message, not a wrong\n"
            "// answer.")
        ackport = "     output wire             p_ack,\n"
        reqblock = "    wire m_req = |s_req;"

    if arb:
        # The requests are ALLOWED to contend here -- that is what the arbiter
        # is for -- so checking s_req would be checking the wrong thing and
        # would fire on correct behaviour.  What must never both be high is the
        # pair of GRANTS, which is a check on bd_arbiter rather than on the
        # caller, and is exactly the claim the mux rests on.
        excl_check = "\n".join([
            "`ifndef SYNTHESIS",
            "    always @(g1 or g2)",
            "        if (g1 === 1'b1 && g2 === 1'b1)",
            f'            $display("  FAIL {name}: both arbiter grants high at %0t -- the mux selects are not exclusive", $time);',
            "`endif"])
    else:
        excl_check = "\n".join([
            "`ifndef SYNTHESIS",
            "    // Not a gate and not synthesised -- a wiring check, so that the",
            "    // one obligation this module places on its caller cannot be",
            "    // broken quietly.",
            "    integer nlive, k;",
            "    always @(s_req) begin",
            "        nlive = 0;",
            f"        for (k = 0; k < {slots}; k = k + 1) nlive = nlive + s_req[k];",
            "        if (nlive > 1)",
            f'            $display("  FAIL {name}: %0d slots requesting at once (s_req=%b) at %0t -- the port mux is one-hot", nlive, s_req, $time);',
            "    end",
            "`endif"])
    return f"""
// memory port, {aw}-bit address, {dw}-bit word ({words}), {slots} slot(s).
// Generated by bdc/mem.py -- do not edit.
//
// DSETUP and DCO are the two matched delays bd_mem's header calls the second
// highest risk in the library: address-and-write-data setup before the
// manufactured clock edge, and clock-to-out before the acknowledge.  They are
// PLACEHOLDERS here.  verify/tighten.py rules B and C size them against the
// vendor's own BRAM_L.sdf windows and name their answer after the ROUTED
// INSTANCE PATH, so the BD_SZ_* keys are spelled at the instance.
//
// Shortening either one is the risky direction: too long costs cycles a
// benchmark will show, too short is a setup violation that a simulation with
// a perfect protocol cannot see and that silicon shows only at some corners.
//
{excl_note}
`default_nettype none
(* keep_hierarchy *)
module {name} #({parlist})
    (input  wire             rst,
     input  wire [{slots - 1}:0]{" " * max(0, 7 - len(str(slots - 1)))}s_req,
     input  wire [{aw * slots - 1}:0]{" " * max(0, 7 - len(str(aw * slots - 1)))}s_addr,
     input  wire [{dw * slots - 1}:0]{" " * max(0, 7 - len(str(dw * slots - 1)))}s_wdata,
     input  wire [{slots - 1}:0]{" " * max(0, 7 - len(str(slots - 1)))}s_we,
{ackport}     output wire [{dw - 1}:0]{dpad}p_rdata);

{reqblock}
{chr(10).join(mux)}

    wire [{n - 1}:0] ram_ack;
{chr(10).join(rams)}

{joinacks}

{excl_check}
endmodule
`default_nettype wire
"""


def emit_proto_top(aw=10, dw=32, module="bdc_mem_top", arb=False):
    """A two-pin top that routes the port and both stations.

    In the shape of cells/verify/soak_top.v, and for the same reason: it is NOT
    a functioning design and is not trying to be.  It exists so that nothing
    folds, nothing merges, and every net is real enough for the router, so the
    gates downstream -- flow.sh, then verify/tighten.py rules B and C -- have a
    routed two-RAM port to measure.

    IT DOES NOT OBEY THE ONE-HOT OBLIGATION.  Both stations are driven from
    independent spine bits, so both slot requests can be high at once, which
    the port module will say so about in simulation.  That is deliberate here
    and it would be a bug anywhere else: what is being asked is "does this
    place, route, and meet the RAM's windows", not "does it compute".

    arb=True routes the OTHER port instead: bd_arbiter in front of the RAM
    gang, `:seq` stations, per-slot acknowledges.  It is a separate top rather
    than a replacement because the two have different things to prove.  The
    plain one is the port whose routed rule-B and rule-C numbers are already
    on record; the arbitrated one adds a mux to the address path and an
    arbiter to the request path, and whether the RAM's setup window survives
    that is a routed question, not a simulated one.  (The arbiter also brings
    its own obligation from bd_arb.v: a consumer must not read a grant within
    one loop delay of the decision.  Here the grant is read by the mux and the
    RAM, which is many hops, but it is a thing to measure and not assume.)

    Two rules from bdc/compute.py's emit_proto_top, both learned the hard way
    and both repeated here because they bite a two-RAM port exactly as they bit
    one unit.  Operands must come from real STATE, or every bit is a function
    of one pin and yosys folds the datapath away.  And the environment must not
    close a COMBINATIONAL loop around the design, or tighten.py sees every
    matched delay as a state node and measures requests arriving at themselves
    -- so every consumer acknowledge here is a LATCH BIT, never a request.
    """
    check(aw, dw)
    nr = ram_count(dw)
    # A wide, non-repeating constant so no two data bits are the same function
    # of one pin -- that is what stops yosys folding the datapath away.
    seed = int("5A3C1E2D" * 4, 16) & ((1 << (dw - 8)) - 1)
    # The `include is half the mechanism, and leaving it out fails SILENTLY:
    # flow.sh accepts BD_SIZES, prints "using measured delay lengths", copies
    # the file to $OUT/sizes.vh, passes -DBD_SIZES -I$OUT -- and if nothing
    # includes it the placeholders below are what actually get built.  This
    # top shipped without it once: verify/resize.sh settled on UMEM0_UCO 6 /
    # UMEM1_UCO 7 and every build in the sweep, including the final one, was
    # routed with the 12-link placeholder.  The gates all passed, because a
    # 12-link chain really does meet rule C; they were just not measuring the
    # design the loop said it had produced.
    szdefs = "`ifdef BD_SIZES\n `include \"sizes.vh\"\n`endif\n" + "\n".join(
        f"`ifndef BD_SZ_UPORT_UMEM{k}_{w}\n"
        f" `define BD_SZ_UPORT_UMEM{k}_{w} {d}\n"
        f"`endif"
        for k in range(nr)
        for w, d in (("USETUP", DEFAULT_DSETUP), ("UCO", DEFAULT_DCO)))
    sfx     = "_seq" if arb else ""
    psfx    = "_arb" if arb else ""
    ackdecl = ("    wire [1:0]           s_ack;" if arb
               else "    wire                 p_ack;")
    ack0    = "s_ack[0]" if arb else "p_ack"
    ack1    = "s_ack[1]" if arb else "p_ack"
    ackport = "s_ack(s_ack)" if arb else "p_ack(p_ack)"
    ackobs  = "s_ack" if arb else "p_ack"
    # The token channels get their own live bits.  They are not a real program
    # order -- nothing here computes -- but they must be distinct signals or
    # the extra join input folds away and the routed cell is the wrong one.
    stok    = "\n        .c_req(p_data_out[1]), .c_ack()," if arb else ""
    ltok    = "\n        .c_req(p_data_out[2]), .c_ack()," if arb else ""
    szargs = ",\n                              ".join(
        f".DSETUP_{k}(`BD_SZ_UPORT_UMEM{k}_USETUP), .DCO_{k}(`BD_SZ_UPORT_UMEM{k}_UCO)"
        for k in range(nr))
    return f"""
// A two-pin top for the memory port and its stations.  Generated by bdc/mem.py.
//
//     BD_OUT=build/pnr/bdcmem BD_TOP_V=build/gen/{module}.v BD_TOP_M={module} \
//         ./flow.sh
//     python3 verify/tighten.py build/pnr/bdcmem/soak.sdf
//
// BD_OUT is not optional: flow.sh names every artifact soak.*, and
// build/pnr/soak.sdf is the tighten gate's own input.
`default_nettype none
module {module} (input wire pin_in, output wire pin_out);

    wire rst = pin_in;

    // A free-running spine: the pipe acknowledges itself, so nothing settles
    // and nothing folds, and there is no combinational path from the design's
    // outputs back to its inputs.
    wire               spine, p_ack_in, p_req_out;
    wire [{dw - 1}:0]  p_data_out;
    bd_delay #(.N(3)) uspin (.a(p_ack_in), .z(spine));
    bd_pipe #(.W({dw}), .N(4)) upipe (
        .rst(rst),
        .req_in(~spine), .ack_in(p_ack_in),
        .data_in({{{dw - 8}'h{seed:x}, 7'h2D, pin_in}}),
        .req_out(p_req_out), .ack_out(p_req_out), .data_out(p_data_out));

    wire [1:0]           s_req, s_we;
    wire [{2 * aw - 1}:0]  s_addr;
    wire [{2 * dw - 1}:0]  s_wdata;
{ackdecl}
    wire [{dw - 1}:0]    p_rdata;

    wire sa_ack, sd_ack, sz_req, la_ack, lz_req;
    wire [{dw - 1}:0] lz_data;

    // Each channel's request gets a DIFFERENT live signal.  Tying them
    // together lets yosys collapse the joins inside the stations into wires.
    bdc_store{sfx}_{aw}_{dw} ust (
        .rst(rst),{stok}
        .a_req(p_req_out), .a_ack(sa_ack), .a_data(p_data_out[{aw - 1}:0]),
        .d_req(spine),     .d_ack(sd_ack), .d_data(p_data_out),
        .z_req(sz_req),    .z_ack(p_data_out[{dw - 1}]),
        .p_req(s_req[0]), .p_ack({ack0}), .p_addr(s_addr[{aw}*0 +: {aw}]),
        .p_wdata(s_wdata[{dw}*0 +: {dw}]), .p_we(s_we[0]), .p_rdata(p_rdata));

    bdc_load{sfx}_{aw}_{dw} uld (
        .rst(rst),{ltok}
        .a_req(p_data_out[0]), .a_ack(la_ack), .a_data(p_data_out[{2 * aw - 1}:{aw}]),
        .z_req(lz_req), .z_ack(p_data_out[{dw - 2}]), .z_data(lz_data),
        .p_req(s_req[1]), .p_ack({ack1}), .p_addr(s_addr[{aw}*1 +: {aw}]),
        .p_wdata(s_wdata[{dw}*1 +: {dw}]), .p_we(s_we[1]), .p_rdata(p_rdata));

    // The delays are placeholders here exactly as they are everywhere else;
    // the point of routing this is to replace them with measured lengths.
    // The BD_SZ_* keys are spelled at the INSTANCE, matching verify/tighten.py's
    // own naming (macro('uport.umem0.usetup') -> BD_SZ_UPORT_UMEM0_USETUP).
{szdefs}
    bdc_memport{psfx}_{aw}_{dw}_2 #({szargs}) uport (
        .rst(rst), .s_req(s_req), .s_addr(s_addr), .s_wdata(s_wdata),
        .s_we(s_we), .{ackport}, .p_rdata(p_rdata));

    // EVERY output is observed.  An output nothing reads is an output the
    // packer is free to delete, and a deleted net is a gate measuring nothing.
    assign pin_out = ^{{lz_data, p_rdata, sz_req, lz_req, sa_ack, sd_ack,
                       la_ack, {ackobs}, s_req, s_we, s_addr, s_wdata,
                       p_data_out, p_req_out, spine}};
endmodule
`default_nettype wire
"""


def emit_all(units, ports=()):
    """`units` is (kind, aw, dw, seq); `ports` is (aw, dw, slots)."""
    seen, out = {}, []
    for aw, dw, slots, arb in ports:
        key = ("port", aw, dw, slots, arb)
        if key in seen:
            continue
        seen[key] = True
        out.append(emit_port(aw, dw, slots, arb))
    for kind, aw, dw, seq in units:
        name = unit_name(kind, aw, dw, seq)
        if name in seen:
            continue
        seen[name] = True
        out.append(emit_unit(kind, aw, dw, seq))
    return ("// Generated by bdc/mem.py -- do not edit.\n"
            "// One module per (kind, address width, word width) actually used.\n"
            + "".join(out))


def main():
    import argparse
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("spec", nargs="+",
                   help="load:AW:DW[:seq], store:AW:DW[:seq], port:AW:DW:SLOTS, portarb:AW:DW:2, top:AW:DW, toparb:AW:DW")
    p.add_argument("-o", "--output")
    a = p.parse_args()
    units, ports, tops = [], [], []
    for s in a.spec:
        parts = s.split(":")
        if parts[0] == "top":
            if len(parts) != 3:
                raise SystemExit(f"bad spec {s!r} -- want top:AW:DW")
            tops.append((int(parts[1]), int(parts[2]), False))
        elif parts[0] == "toparb":
            if len(parts) != 3:
                raise SystemExit(f"bad spec {s!r} -- want toparb:AW:DW")
            tops.append((int(parts[1]), int(parts[2]), True))
        elif parts[0] == "portarb":
            if len(parts) != 4:
                raise SystemExit(f"bad spec {s!r} -- want portarb:AW:DW:SLOTS")
            ports.append((int(parts[1]), int(parts[2]), int(parts[3]), True))
        elif parts[0] == "port":
            if len(parts) != 4:
                raise SystemExit(f"bad spec {s!r} -- want port:AW:DW:SLOTS")
            ports.append((int(parts[1]), int(parts[2]), int(parts[3]), False))
        elif len(parts) == 4 and parts[3] == "seq":
            units.append((parts[0], int(parts[1]), int(parts[2]), True))
        elif len(parts) == 3:
            units.append((parts[0], int(parts[1]), int(parts[2]), False))
        else:
            raise SystemExit(f"bad spec {s!r} -- want kind:AW:DW")
    text = emit_all(units, ports)
    for aw, dw, arb in tops:
        text += emit_proto_top(aw, dw, module="bdc_mem_arb_top" if arb else "bdc_mem_top",
                               arb=arb)
    if a.output:
        with open(a.output, "w") as f:
            f.write(text)
    else:
        print(text)


if __name__ == "__main__":
    main()
