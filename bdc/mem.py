#!/usr/bin/env python3
"""Stage 6 groundwork: one memory ACCESS, as a bundled-data cell.

THE RESULT THIS FILE EXISTS TO RECORD

A load is a compute unit whose function is the RAM.  Not "like" one -- the
same wiring, arc for arc.  bdc/compute.py builds every arithmetic cell as

    bd_join over the operands  ->  joined ;  every operand's ack = z_ack
    z_req  = delta(joined)                    <- bd_delay, sized post-route
    z_data = f(operand data)                  <- combinational

and bd_mem is already exactly that shape with the delay inside it:

    bd_mem.req  = joined
    bd_mem.ack  = z_req          <- DSETUP + the explicit clock buffer + DCO
    bd_mem.rdata = z_data        <- the RAM, clocked by the request itself

So a single-port access needs NO new controller, and that is worth stating
because the obvious first draft is a hand-built four-phase sequencer with a
capture latch, a done C-element and a return-to-zero detector.  None of it is
needed.  Substituting bd_mem for the bd_delay is the whole cell.

WHY THE RETURN-TO-ZERO ORDERING FALLS OUT FOR FREE

bd_mem's header names "pipelined return-to-zero overlap" as a failure this
cell owns: back-to-back accesses whose reset phases overlap corrupt the port.
With one station on one port that cannot happen, and the reason is the
four-phase hold window rather than any timing argument.  Trace it:

    z_ack rises      the consumer has taken the loaded value
    joined falls     because bd_join's ack_out is z_ack, so the address
                       channel's request drops
    bd_mem.req falls
    ram_clk falls    DSETUP later
    ack falls        DCO after that, so z_req falls
    z_ack falls      the consumer's latch closes on data that is still
                       being held -- rdata does not move until the next
                       manufactured edge, and there cannot be one yet
    address released only now, and only now can the next request rise

The next manufactured clock edge requires the address channel to be free,
which requires z_ack to have fallen, which is strictly after ack fell.  The
port is fully returned to zero before it is asked for anything again.  This is
correct by construction and needs no delay to make it so.

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

WHAT THIS FILE DELIBERATELY DOES NOT SOLVE

Who guarantees that one-hotness, and in what order the slots fire.  That is
program-order serialisation -- handshake's `mem_controller` -- and bdc/MEMORY.md
records how far the design got and the one ordering assumption that is not yet
correct by construction.  Nothing here assumes an answer: a caller that
sequences the slots itself (as cells/tb/tb_bdc_mem.v does) is using this file
exactly as intended.

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


def unit_name(kind, aw, dw):
    if kind not in ("load", "store"):
        raise MemError(f"no memory unit for {kind!r} -- load or store")
    return f"bdc_{kind}_{aw}_{dw}"


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


def emit_unit(kind, aw, dw):
    """One memory access STATION as a self-contained Verilog module.

    It owns no RAM.  It drives one slot of a bdc_memport and is otherwise the
    same shape as an arithmetic unit from bdc/compute.py: join the operands,
    hand them to the boundary, and let the boundary's own acknowledge be this
    cell's outgoing request.
    """
    check(aw, dw)
    name = unit_name(kind, aw, dw)
    store = kind == "store"

    # Input channels.  A load consumes the address; a store consumes the
    # address and the value.  Both are a JOIN: the RAM boundary means nothing
    # until every operand has arrived, exactly as for an arithmetic unit.
    chans = ["a"] + (["d"] if store else [])
    cw = {"a": aw, "d": dw}

    decls = []
    for c in chans:
        pad = " " * max(0, 7 - len(str(cw[c] - 1)))
        decls += [f"     input  wire             {c}_req,",
                  f"     output wire             {c}_ack,",
                  f"     input  wire [{cw[c] - 1}:0]{pad}{c}_data,"]

    req_cat = ("{" + ", ".join(f"{c}_req" for c in reversed(chans)) + "}"
               if len(chans) > 1 else "a_req")
    ack_cat = ("{" + ", ".join(f"{c}_ack" for c in reversed(chans)) + "}"
               if len(chans) > 1 else "a_ack")

    dpad = " " * max(0, 7 - len(str(dw - 1)))
    apad = " " * max(0, 7 - len(str(aw - 1)))
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
    // The acknowledge goes back to ALL of them together and it is z_ack, so
    // the address and the write data are held until the consumer's own latch
    // has closed -- which is what puts the whole return-to-zero phase of the
    // port inside the operands' hold window.  See bdc/mem.py's header.
    wire joined;
    bd_join #(.N({len(chans)})) ujoin (
        .rst(rst), .req_in({req_cat}), .ack_out({ack_cat}),
        .req(joined), .ack(z_ack));

    assign p_req   = joined;
    assign p_addr  = a_data;
    assign p_wdata = {"d_data" if store else f"{dw}'b0"};
    assign p_we    = 1'b{1 if store else 0};

    // The port's acknowledge IS this cell's outgoing request.  That is the
    // whole substitution this file is about: bd_mem's DSETUP + buffer + DCO
    // stands exactly where bdc/compute.py puts its bd_delay.
    //
    // It is gated by this station's own claim, and the gate is not optional.
    // p_ack is SHARED: without the gate, the next slot's acknowledge would
    // look like a second result on this channel.  joined falls when z_ack
    // rises, so the gate drops z_req after its acknowledge, which is the
    // four-phase order and not an early release.
    (* keep *) LUT2 #(.INIT(4'h8)) uzr (.I0(p_ack), .I1(joined), .O(z_req));
{"" if store else "    assign z_data  = p_rdata;"}
endmodule
`default_nettype wire
"""


def emit_port(aw, dw, slots=1):
    """The RAM gang and its slot mux, as a self-contained Verilog module."""
    check(aw, dw)
    n = ram_count(dw)
    name = f"bdc_memport_{aw}_{dw}_{slots}"

    dpad = " " * max(0, 7 - len(str(dw - 1)))
    apad = " " * max(0, 7 - len(str(aw - 1)))

    # One-hot AND-OR mux.  At most one slot's request is high, so an OR of
    # masked payloads is the whole selector -- no priority, no encoder, and
    # nothing that changes value while a request is high, because the slot
    # holding the request is the only one contributing.
    mux = []
    for sig, w in (("addr", aw), ("wdata", dw)):
        terms = " |\n                    ".join(
            f"({{{w}{{s_req[{k}]}}}} & s_{sig}[{w}*{k} +: {w}])"
            for k in range(slots))
        mux.append(f"    wire [{w - 1}:0] m_{sig} = {terms};")
    weterms = " | ".join(f"(s_req[{k}] & s_we[{k}])" for k in range(slots))
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
            f"             .DSETUP(DSETUP), .DCO(DCO), .USE_BUFG(0)) umem{i} (",
            f"        .req(m_req), .ack(ram_ack[{i}]),",
            f"        .addr(m_addr), .wdata({wd}), .we(m_we),",
            f"        .rdata({rd}));",
        ]

    if n == 1:
        joinacks = "    assign p_ack = ram_ack[0];"
    else:
        joinacks = (
            "    // Every word has answered before the acknowledge rises, and\n"
            "    // every word has reset before it falls.  A C-tree is the only\n"
            "    // gate that means both.  It sits AFTER each DCO, which\n"
            "    // lengthens the acknowledge -- the safe direction, and the\n"
            "    // direction rule C's margin then understates.\n"
            f"    bd_ctree #(.N({n})) uackj (.a(ram_ack), .rst(rst), .q(p_ack));")

    words = f"{n} x {RAM_DW} bits" if n > 1 else f"{RAM_DW} bits"
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
// AT MOST ONE SLOT REQUEST MAY BE HIGH AT A TIME.  The mux below is a one-hot
// AND-OR and says nothing useful about two live slots; worse, two live slots
// mean the RAM's manufactured clock never falls between them, so there is no
// second edge and the second access silently does not happen.  Enforcing that
// is the caller's job -- see bdc/MEMORY.md.  This module checks it in
// simulation so that a wiring mistake is a message rather than a wrong answer.
`default_nettype none
(* keep_hierarchy *)
module {name} #(parameter DSETUP = {DEFAULT_DSETUP}, parameter DCO = {DEFAULT_DCO})
    (input  wire             rst,
     input  wire [{slots - 1}:0]{" " * max(0, 7 - len(str(slots - 1)))}s_req,
     input  wire [{aw * slots - 1}:0]{" " * max(0, 7 - len(str(aw * slots - 1)))}s_addr,
     input  wire [{dw * slots - 1}:0]{" " * max(0, 7 - len(str(dw * slots - 1)))}s_wdata,
     input  wire [{slots - 1}:0]{" " * max(0, 7 - len(str(slots - 1)))}s_we,
     output wire             p_ack,
     output wire [{dw - 1}:0]{dpad}p_rdata);

    wire m_req = |s_req;
{chr(10).join(mux)}

    wire [{n - 1}:0] ram_ack;
{chr(10).join(rams)}

{joinacks}

`ifndef SYNTHESIS
    // Not a gate and not synthesised -- a wiring check, so that the one
    // obligation this module places on its caller cannot be broken quietly.
    integer nlive, k;
    always @(s_req) begin
        nlive = 0;
        for (k = 0; k < {slots}; k = k + 1) nlive = nlive + s_req[k];
        if (nlive > 1)
            $display("  FAIL {name}: %0d slots requesting at once (s_req=%b) "
                     "at %0t -- the port mux is one-hot", nlive, s_req, $time);
    end
`endif
endmodule
`default_nettype wire
"""


def emit_all(units, ports=()):
    """`units` is (kind, aw, dw); `ports` is (aw, dw, slots).  One Verilog file."""
    seen, out = {}, []
    for aw, dw, slots in ports:
        key = ("port", aw, dw, slots)
        if key in seen:
            continue
        seen[key] = True
        out.append(emit_port(aw, dw, slots))
    for kind, aw, dw in units:
        name = unit_name(kind, aw, dw)
        if name in seen:
            continue
        seen[name] = True
        out.append(emit_unit(kind, aw, dw))
    return ("// Generated by bdc/mem.py -- do not edit.\n"
            "// One module per (kind, address width, word width) actually used.\n"
            + "".join(out))


def main():
    import argparse
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("spec", nargs="+",
                   help="load:AW:DW, store:AW:DW, or port:AW:DW:SLOTS")
    p.add_argument("-o", "--output")
    a = p.parse_args()
    units, ports = [], []
    for s in a.spec:
        parts = s.split(":")
        if parts[0] == "port":
            if len(parts) != 4:
                raise SystemExit(f"bad spec {s!r} -- want port:AW:DW:SLOTS")
            ports.append((int(parts[1]), int(parts[2]), int(parts[3])))
        elif len(parts) == 3:
            units.append((parts[0], int(parts[1]), int(parts[2])))
        else:
            raise SystemExit(f"bad spec {s!r} -- want kind:AW:DW")
    text = emit_all(units, ports)
    if a.output:
        with open(a.output, "w") as f:
            f.write(text)
    else:
        print(text)


if __name__ == "__main__":
    main()
