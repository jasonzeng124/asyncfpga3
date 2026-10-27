`timescale 1ps/1ps
`define GLS_FID
// ---------------------------------------------------------------------------
// fid_core.vh -- the opt-in "silicon-like" primitive core (F3).  Included by
// gls/prims.v under GLS_FID and by sim/bd_prims_sim.v under BD_FID; nothing
// here is compiled into the default GLS or the default cell simulation.
//
// research/data/fid/f3_model.md has the measurements and the negative
// controls.  In short:
//
// 1. TRANSPORT PER PIN.  Each LUT input is delayed by ITS OWN arc as a
//    transport delay (a nonblocking assignment with intra-assignment delay,
//    which keeps every edge), and the output is the zero-time mux tree of the
//    DELAYED inputs.  So: no "sample at fire" early edge (the default model's
//    specify path copies f at fire time, gls audit 1a/5), pulses of any width
//    pass (pessimistic for async; no published 7-series LUT pulse-rejection
//    figure was found), and a multi-input change produces the function hazard
//    its arrival order implies.  A single-input change that leaves f unchanged
//    produces no edge, consistent with Xilinx's informal claim that a LUT does
//    not glitch on a single-input change (P. Alfke, comp.arch.fpga; not a
//    datasheet guarantee).  Internal mux-tree skew beyond the characterised
//    per-pin arcs is unknown; +FID_LEVEL_PS=s adds (3.5-k)*s ps to pin Ak
//    (A6 at the root, fastest) to explore it.  Default 0 (assumption, stated).
//
// 2. METASTABILITY on a STATE node: a LUT output that feeds back into its own
//    input (C-element, latch, arbiter state), loop delay TLOOP = feedback wire
//    + the feedback pin's arc.  When the output reverses less than TLOOP
//    after its last edge, the drive was removed before the loop could commit:
//    a runt.  With p = runt width and an offset
//        delta = p - (TLOOP - WIN/2) + N(0, WIN/4)        (thermal noise)
//      delta <= -WIN/2 : the runt is rejected outright (the node never left);
//      otherwise       : the node resolves to the runt value if delta > 0,
//                        else back, after t_r = TAU*ln(WIN/(2|delta|)) >= 0,
//    i.e. the textbook law t_r = tau ln(T0/|dt|), which for a uniformly
//    distributed offset gives the exponential tail P(t_r > t) ~ exp(-t/tau).
//    During resolution the node holds the runt-end value (or X with
//    +META_X=1); the loop's own echo of the runt is ignored until TLOOP after
//    resolution, then the node is re-evaluated against its function (a
//    genuine input change inside that window is applied late, not lost).
//    TAU/WIN for a LUT loop are not published anywhere found; defaults
//    TAU=WIN=150 ps are an assumption (see f3_model.md), plusargs
//    +META_TAU=, +META_WIN=, +META_SEED=, +META_VERBOSE=1, +META_OFF=1 (the
//    resolver disabled: pure transport, the ablation the negative controls use).
// ---------------------------------------------------------------------------

`ifndef FID_CORE_VH
`define FID_CORE_VH

module FID_RESOLVE (input wire f, input wire en, output wire o);
    parameter integer TLOOP = 0;
    parameter integer SEED  = 1;
    parameter integer TAU   = 150;
    parameter integer WIN   = 150;
    integer tau, win, seed, gseed, verbose, xmode, off;
    integer n_meta, n_rej, n_commit;
    reg o_r = 1'bx;
    assign o = o_r;
    reg kick = 1'b0, busy = 1'b0, v_before = 1'bx, runt_val, choose;
    time t_last = 0, ign_until = 0, p;
    integer noise, delta, ad, trp;
    real trr;
    initial begin
        tau = TAU; win = WIN; gseed = 0; verbose = 0; xmode = 0; off = 0;
        if ($value$plusargs("META_OFF=%d", off)) ;   // ablation: transport only
        n_meta = 0; n_rej = 0; n_commit = 0;
        if ($value$plusargs("META_TAU=%d", tau)) ;
        if ($value$plusargs("META_WIN=%d", win)) ;
        if ($value$plusargs("META_SEED=%d", gseed)) ;
        if ($value$plusargs("META_VERBOSE=%d", verbose)) ;
        if ($value$plusargs("META_X=%d", xmode)) ;
        seed = SEED * 7919 + gseed * 104729 + 17;
    end
    always @(f or kick) begin
        if (en !== 1'b1 || TLOOP == 0 || off) begin
            o_r = f;
        end else if (busy || $time < ign_until) begin
            ;                                   // re-evaluated by kick
        end else if (f !== o_r) begin
            if ((f === 1'b0 || f === 1'b1) && (o_r === 1'b0 || o_r === 1'b1)
                    && t_last > 0 && f === v_before && ($time - t_last) < TLOOP) begin
                p = $time - t_last;
                runt_val = o_r;
                noise = $dist_normal(seed, 0, (win > 4) ? win / 4 : 1);
                delta = p - (TLOOP - win / 2) + noise;
                if (delta <= -(win / 2)) begin
                    n_rej = n_rej + 1;
                    if (verbose > 1)
                        $display("RUNT %m t=%0t runt=%0t loop=%0d rejected", $time, p, TLOOP);
                    o_r = f;
                    t_last = 0;
                    ign_until = $time + TLOOP + 1;
                    kick <= #(TLOOP + 1) ~kick;
                end else begin
                    choose = (delta > 0) ? runt_val : f;
                    ad = (delta < 0) ? -delta : delta;
                    if (ad < 1) ad = 1;
                    if (2 * ad < win) begin
                        trr = tau * $ln((1.0 * win) / (2.0 * ad));
                        trp = (trr > 40.0 * tau) ? 40 * tau : $rtoi(trr);
                    end else trp = 0;
                    n_meta = n_meta + 1;
                    if (choose === runt_val) n_commit = n_commit + 1;
                    if (verbose)
                        $display("META %m t=%0t runt=%0t loop=%0d delta=%0d runt_val=%b -> %b after %0d ps",
                                 $time, p, TLOOP, delta, runt_val, choose, trp);
                    o_r = xmode ? 1'bx : f;
                    busy = 1'b1;
                    t_last = 0;
                    ign_until = $time + trp + TLOOP + 1;
                    o_r  <= #(trp) choose;
                    busy <= #(trp) 1'b0;
                    kick <= #(trp + TLOOP + 1) ~kick;
                end
            end else begin
                v_before = o_r;
                o_r = f;
                t_last = $time;
            end
        end
    end
endmodule

// f, 1 ps later, without its zero-width glitches (see FID_LUT6).
module FID_SAMPLE (input wire f, output reg o);
    reg armed = 1'b0;
    initial o = 1'bx;
    always @(f) if (!armed) begin
        armed = 1'b1;
        #1;
        armed = 1'b0;
        o = f;
    end
endmodule

// The LUT6 with both outputs.  O6 = INIT[A6..A1], O5 = INIT[31:0][A5..A1].
// T<k>_6 / T<k>_5 are the per-pin arcs to O6 / O5.  EN6/EN5 turn the state
// resolver on for that output (static from gen.py, or the run-time feedback
// detector in bd_prims_sim.v).
module FID_LUT6 (input wire A1, A2, A3, A4, A5, A6,
                 input wire EN6, EN5,
                 output wire O5, O6);
    parameter [63:0] INIT = 64'h0;
    parameter integer T1_6 = 124, T2_6 = 124, T3_6 = 124, T4_6 = 124, T5_6 = 124, T6_6 = 124;
    parameter integer T1_5 = 124, T2_5 = 124, T3_5 = 124, T4_5 = 124, T5_5 = 124;
    parameter integer TLOOP6 = 0, TLOOP5 = 0;
    parameter integer SEED = 1;
    integer lv, d1, d2, d3, d4, d5, d6, e1, e2, e3, e4, e5;
    initial begin
        lv = 0;
        if ($value$plusargs("FID_LEVEL_PS=%d", lv)) ;
        // A6 is the root select (fastest internally), A1 the leaf.
        // every pin is delayed by its arc minus the 1 ps the output sampler
        // below adds back
        d1 = T1_6 + (5 * lv) / 2 - 1; d2 = T2_6 + (3 * lv) / 2 - 1; d3 = T3_6 + lv / 2 - 1;
        d4 = T4_6 - lv / 2 - 1;       d5 = T5_6 - (3 * lv) / 2 - 1; d6 = T6_6 - (5 * lv) / 2 - 1;
        e1 = T1_5 + 2 * lv - 1; e2 = T2_5 + lv - 1; e3 = T3_5 - 1; e4 = T4_5 - lv - 1; e5 = T5_5 - 2 * lv - 1;
        if (d1 < 0) d1 = 0; if (d2 < 0) d2 = 0; if (d3 < 0) d3 = 0;
        if (d4 < 0) d4 = 0; if (d5 < 0) d5 = 0; if (d6 < 0) d6 = 0;
        if (e1 < 0) e1 = 0; if (e2 < 0) e2 = 0; if (e3 < 0) e3 = 0;
        if (e4 < 0) e4 = 0; if (e5 < 0) e5 = 0;
    end
    reg a1 = 1'bx, a2 = 1'bx, a3 = 1'bx, a4 = 1'bx, a5 = 1'bx, a6 = 1'bx;
    reg b1 = 1'bx, b2 = 1'bx, b3 = 1'bx, b4 = 1'bx, b5 = 1'bx;
    // A pin whose value is set at elaboration (a tie-off, a reg with an
    // initialiser) produces no event, so every pin is also sampled once at
    // time 0 -- otherwise its delayed copy would stay x forever.
    initial begin
        #0;
        a1 <= #(d1) A1; a2 <= #(d2) A2; a3 <= #(d3) A3;
        a4 <= #(d4) A4; a5 <= #(d5) A5; a6 <= #(d6) A6;
        b1 <= #(e1) A1; b2 <= #(e2) A2; b3 <= #(e3) A3;
        b4 <= #(e4) A4; b5 <= #(e5) A5;
    end
    always @(A1) a1 <= #(d1) A1;
    always @(A2) a2 <= #(d2) A2;
    always @(A3) a3 <= #(d3) A3;
    always @(A4) a4 <= #(d4) A4;
    always @(A5) a5 <= #(d5) A5;
    always @(A6) a6 <= #(d6) A6;
    always @(A1) b1 <= #(e1) A1;
    always @(A2) b2 <= #(e2) A2;
    always @(A3) b3 <= #(e3) A3;
    always @(A4) b4 <= #(e4) A4;
    always @(A5) b5 <= #(e5) A5;

    // Mux tree with A6 at the root, as on the die (UG474: two LUT5s and a
    // mux on A6).  X behaviour is the same Kleene resolution as the default
    // model: a select at x resolves whenever both branches agree.
    // Evaluation order does not change a 0/1 result; for x it is the same
    // Kleene function either way (a mux tree resolves x iff the branches
    // agree, whatever the order), so the tree is written leaf-first like the
    // default model and the root/leaf distinction lives in the delays above.
    wire [31:0] u5 = a6 ? INIT[63:32] : INIT[31:0];
    wire [15:0] u4 = a5 ?   u5[31:16] :   u5[15:0];
    wire [ 7:0] u3 = a4 ?   u4[15:8]  :   u4[7:0];
    wire [ 3:0] u2 = a3 ?   u3[7:4]   :   u3[3:0];
    wire [ 1:0] u1 = a2 ?   u2[3:2]   :   u2[1:0];
    wire f6 = a1 ? u1[1] : u1[0];

    wire [15:0] v4 = b5 ? INIT[31:16] : INIT[15:0];
    wire [ 7:0] v3 = b4 ?   v4[15:8]  :   v4[7:0];
    wire [ 3:0] v2 = b3 ?   v3[7:4]   :   v3[3:0];
    wire [ 1:0] v1 = b2 ?   v2[3:2]   :   v2[1:0];
    wire f5 = b1 ? v1[1] : v1[0];

    // Two pins whose delayed copies land in the same time step update one
    // after the other, so f can glitch for zero time between them -- a
    // simulator artefact (it once fed the resolver a 0 ps "runt").  The
    // sampler takes f 1 ps after its first change, once per step.
    wire f6s, f5s;
    FID_SAMPLE s6 (.f(f6), .o(f6s));
    FID_SAMPLE s5 (.f(f5), .o(f5s));
    FID_RESOLVE #(.TLOOP(TLOOP6), .SEED(2 * SEED + 1)) r6 (.f(f6s), .en(EN6), .o(O6));
    FID_RESOLVE #(.TLOOP(TLOOP5), .SEED(2 * SEED))     r5 (.f(f5s), .en(EN5), .o(O5));
endmodule

// Transport 2:1 mux (MUXF7/MUXF8 and anything shaped like one).
module FID_MUX2 (input wire D0, D1, S0, output wire OUT);
    parameter integer TD0 = 104, TD1 = 104, TS0 = 273;
    localparam integer E0 = (TD0 > 0) ? TD0 - 1 : 0, E1 = (TD1 > 0) ? TD1 - 1 : 0,
                       ES = (TS0 > 0) ? TS0 - 1 : 0;
    reg d0 = 1'bx, d1 = 1'bx, s0 = 1'bx;
    initial begin #0; d0 <= #(E0) D0; d1 <= #(E1) D1; s0 <= #(ES) S0; end
    always @(D0) d0 <= #(E0) D0;
    always @(D1) d1 <= #(E1) D1;
    always @(S0) s0 <= #(ES) S0;
    wire f = s0 ? d1 : d0;
    FID_SAMPLE s (.f(f), .o(OUT));
endmodule

`endif
// ---------------------------------------------------------------------------
// prims.v -- simulation models for the bel-level primitives nextpnr-xilinx
// emits in gcd_hw_routed.json, shaped so that EVERY timing arc the routed SDF
// annotates has a specify path to land on.
//
// These are not Xilinx UNISIMs.  SLICE_LUTX / SELMUX2_1 / SLICE_FFX / ICBUF are
// nextpnr-xilinx bel names (and, for ICBUF, this flow's own), and there is no
// vendor model for them.  They are written against nextpnr-xilinx's sources
// (xilinx/pack.cc, xilinx/fasm.cc) for what each bel port means.
//
// TIMING LIVES ENTIRELY IN THE SPECIFY BLOCKS.  There is no #delay on any
// behavioural assignment.  iverilog's module-path delays are real delays on the
// output net -- verified on a two-inverter probe -- so a specify path is
// sufficient to break the zero-time feedback loops this netlist is full of
// (every C-element and every latch in the library is a LUT feeding its own
// input).  Mixing an assign delay with a path delay would add the two, so the
// assigns carry none and every number in the simulation comes from the SDF.
//
// The default values below are nextpnr's own nominal arcs and are what an arc
// gets if the SDF does not annotate it.  On this design that set is exactly the
// arcs nextpnr's timing model omits because the pin is tied off or the function
// does not read it -- proved, not assumed: no unrouted LUT pin in this netlist
// carries a live dependence.  They are never zero, so no combinational loop can
// close in zero time.
//
// SLICE_LUTX INIT is PHYSICALLY addressed (A1 = bit 0).  gen.py pre-applies
// nextpnr's X_ORIG_PORT_A<n> permutation, so this module is a plain decoder.
// ---------------------------------------------------------------------------

`timescale 1ps/1ps
`default_nettype none
`ifdef GLS_FID

`endif

// ---- ICBUF ------------------------------------------- one routed net hop --
// One instance per INTERCONNECT entry in the routed SDF, i.e. one per sink
// pin.  This exists because iverilog 11 parses (INTERCONNECT ...) and then
// applies nothing -- so the only way to get nextpnr's routed wire delays into
// the simulation is to make each of them an IOPATH on a cell of its own.
// It also makes the fanout of a driver arrive at its sinks at different times,
// which is the physical truth and is exactly what a bundled-data design's
// margin is spent on.
// The delay is a PARAMETER as well as an SDF target: netlist.v leaves it at
// the default and lets $sdf_annotate fill it in (that is the acceptance-gate
// build), while netlist_baked.v sets it from the same parsed SDF number at
// generation time.  Both carry identical delays -- proved by diffing a run --
// and the baked one exists only because iverilog's annotator does a linear
// scope scan per entry, which on 58k instances costs minutes of wall clock
// before time 0.
// A wire is a TRANSPORT delay: FPGA interconnect is a chain of buffers, so a
// pulse narrower than the wire's delay still comes out the far end.  iverilog's
// module-path delay is not that -- with more than one edge in flight it drops
// edges (a 906 ps pulse into a 1245 ps path never arrives, and two pulses 300
// ps apart lose their second rise), which read as a latch that never opened.
// Four-phase control never puts two edges of one wire within a wire delay of
// each other, so it was never caught out (a data cone's glitches are, and a
// dropped one hides a hazard rather than inventing one); a two-phase link's
// enable pulse is exactly that wide.  The baked build (-DGLS_TRANSPORT_IC) uses a
// nonblocking transport assignment; the annotated build keeps the specify
// path, which is what $sdf_annotate attaches its IOPATH to.
module ICBUF (input wire I, output wire O);
    parameter D = 1;
`ifdef GLS_TRANSPORT_IC
    reg o = 1'bx;
    always @(I) o <= #D I;
    assign O = o;
`else
    assign O = I;
    specify (I => O) = D; endspecify
`endif
endmodule

`ifndef GLS_FID
// ---- SLICE_LUTX --------------------------------------------------- 1 LUT --
// One nextpnr SLICE_LUTX bel drives exactly one of O5/O6 (checked: no cell in
// this design connects both).  O6 is the full six-input function; O5 is
// architecturally restricted to A1..A5 and reads INIT[31:0].
module SLICE_LUTX (
    input  wire A1, A2, A3, A4, A5, A6,
    output wire O5, O6
);
    parameter [63:0] INIT = 64'h0;
    parameter TA1O6=124, TA2O6=124, TA3O6=124, TA4O6=124, TA5O6=124, TA6O6=124;
    parameter TA1O5=124, TA2O5=124, TA3O5=124, TA4O5=124, TA5O5=124;
    // read only by the GLS_FID model; accepted here so one testbench
    // elaborates against both
    parameter integer META6 = 0, META5 = 0, TLOOP6 = 0, TLOOP5 = 0, SEED = 1;

    wire [31:0] s5 = A6 ? INIT[63:32] : INIT[31:0];
    wire [15:0] s4 = A5 ?   s5[31:16] :   s5[15:0];
    wire [ 7:0] s3 = A4 ?   s4[15:8]  :   s4[7:0];
    wire [ 3:0] s2 = A3 ?   s3[7:4]   :   s3[3:0];
    wire [ 1:0] s1 = A2 ?   s2[3:2]   :   s2[1:0];
    assign O6 = A1 ? s1[1] : s1[0];

    wire [15:0] t4 = A5 ? INIT[31:16] : INIT[15:0];
    wire [ 7:0] t3 = A4 ?   t4[15:8]  :   t4[7:0];
    wire [ 3:0] t2 = A3 ?   t3[7:4]   :   t3[3:0];
    wire [ 1:0] t1 = A2 ?   t2[3:2]   :   t2[1:0];
    assign O5 = A1 ? t1[1] : t1[0];

    specify
        (A1 => O6) = TA1O6; (A2 => O6) = TA2O6; (A3 => O6) = TA3O6;
        (A4 => O6) = TA4O6; (A5 => O6) = TA5O6; (A6 => O6) = TA6O6;
        (A1 => O5) = TA1O5; (A2 => O5) = TA2O5; (A3 => O5) = TA3O5;
        (A4 => O5) = TA4O5; (A5 => O5) = TA5O5;
    endspecify
endmodule

`else
// GLS_FID (opt-in, cells/gls/fid_core.vh): per-pin TRANSPORT arcs, output =
// mux tree of the delayed pins, and a metastability resolver on a state node.
// gen.py (GLS_MODEL=fid) sets META6/META5 = 1 and TLOOP6/TLOOP5 = feedback
// wire + arc on a LUT whose output is routed back into one of its own pins,
// and SEED = the cell's index.
module SLICE_LUTX (
    input  wire A1, A2, A3, A4, A5, A6,
    output wire O5, O6
);
    parameter [63:0] INIT = 64'h0;
    parameter TA1O6=124, TA2O6=124, TA3O6=124, TA4O6=124, TA5O6=124, TA6O6=124;
    parameter TA1O5=124, TA2O5=124, TA3O5=124, TA4O5=124, TA5O5=124;
    parameter integer META6 = 0, META5 = 0, TLOOP6 = 0, TLOOP5 = 0, SEED = 1;
    FID_LUT6 #(.INIT(INIT),
        .T1_6(TA1O6), .T2_6(TA2O6), .T3_6(TA3O6), .T4_6(TA4O6), .T5_6(TA5O6), .T6_6(TA6O6),
        .T1_5(TA1O5), .T2_5(TA2O5), .T3_5(TA3O5), .T4_5(TA4O5), .T5_5(TA5O5),
        .TLOOP6(TLOOP6), .TLOOP5(TLOOP5), .SEED(SEED)) u (
        .A1(A1), .A2(A2), .A3(A3), .A4(A4), .A5(A5), .A6(A6),
        .EN6(META6 ? 1'b1 : 1'b0), .EN5(META5 ? 1'b1 : 1'b0), .O5(O5), .O6(O6));
endmodule
`endif

`ifndef GLS_FID
// ---- SELMUX2_1 ------------------------------------------ MUXF7 / MUXF8 --
// The bel's two data pins are named by the bare digits 0 and 1 in both the
// JSON and the SDF.  gen.py renames them D0/D1 on BOTH sides of the rewrite,
// so nothing here has to be an escaped identifier.
module SELMUX2_1 (
    input  wire D0, D1, S0,
    output wire OUT
);
    parameter TD0OUT=104, TD1OUT=104, TS0OUT=273;
    assign OUT = S0 ? D1 : D0;
    specify
        (D0 => OUT) = TD0OUT; (D1 => OUT) = TD1OUT; (S0 => OUT) = TS0OUT;
    endspecify
endmodule

`else
module SELMUX2_1 (
    input  wire D0, D1, S0,
    output wire OUT
);
    parameter TD0OUT=104, TD1OUT=104, TS0OUT=273;
    FID_MUX2 #(.TD0(TD0OUT), .TD1(TD1OUT), .TS0(TS0OUT)) u (.D0(D0), .D1(D1), .S0(S0), .OUT(OUT));
endmodule
`endif

`ifndef GLS_FID
// ---- SLICE_FFX ------------------------------------------ FDRE and FDSE --
// Both map to this bel and they differ only in what SR does.  X_ORIG_PORT_SR
// records which: "R" -> synchronous reset to 0, "S" -> synchronous set to 1.
// gen.py passes it as SRVAL.  20 of the 247 flops here are FDSE, and gcd_hw's
// rst_sr is built out of them -- modelled as FDRE it would never assert the
// rig's reset at all.  INIT is the configuration (global set/reset) value.
module SLICE_FFX (
    input  wire CK, D, CE, SR,
    output reg  Q
);
    parameter [0:0] INIT  = 1'b0;
    parameter [0:0] SRVAL = 1'b0;
    parameter TCKQ = 100;
    // The SDF's SETUPHOLD for this bel.  iverilog applies no TIMINGCHECK, so
    // the check is behavioural: a D (or CE) change inside TSU before or THD
    // after a rising CK is reported, and the flop goes X, which the vector
    // compare then catches.  TSU/THD 0 (no SETUPHOLD in the SDF) checks
    // nothing.
    parameter TSU = 0;
    parameter THD = 0;
    parameter integer SEED = 1;     // read only by the GLS_FID model
    initial Q = INIT;
    time t_ck = 0, t_in = 0;

    always @(posedge CK) begin
        if (TSU > 0 && t_in > 0 && $time - t_in < TSU) begin
            $display("FF SETUP VIOLATION %m at %0t (input moved %0t ago)",
                     $time, $time - t_in);
            Q <= 1'bx;
        end else if (SR) Q <= SRVAL;
        else if (CE)     Q <= D;
        t_ck = $time;
    end

    always @(D or CE) begin
        if (THD > 0 && t_ck > 0 && $time - t_ck < THD) begin
            $display("FF HOLD VIOLATION %m at %0t (CK rose %0t ago)",
                     $time, $time - t_ck);
            Q <= 1'bx;
        end
        t_in = $time;
    end

    specify
        (posedge CK => (Q +: D)) = TCKQ;
    endspecify
endmodule

`else
// GLS_FID: an input change inside the FF's aperture [-TSU, +THD] around a
// rising CK does not go X; the flop resolves to the old or the new value
// (offset from the aperture centre plus N(0, ap/4) noise picks which) after
// an extra t_r = TAU_FF*ln(ap/(2|delta|)), i.e. an exponential tail.  Without
// a SETUPHOLD in the SDF the aperture is +META_FFW= (default 50 ps), centred.
// TAU_FF default 75 ps (+META_TAU_FF=): at or above every FPGA flop tau in
// Beer et al., ASYNC 2010 (57/51/73 ps at 130/90/65 nm); no 28 nm 7-series
// figure was found, and a longer tau is the pessimistic side.
module SLICE_FFX (
    input  wire CK, D, CE, SR,
    output reg  Q
);
    parameter [0:0] INIT  = 1'b0;
    parameter [0:0] SRVAL = 1'b0;
    parameter TCKQ = 100;
    parameter TSU = 0;
    parameter THD = 0;
    parameter integer SEED = 1;
    integer tau, wff, seed, gseed, verbose, tsu, thd, ap, c0, x, noise, delta, ad, trp;
    integer n_meta;
    real trr;
    reg d_last, ce_last, oldv, newv, choose;
    initial begin
        Q = INIT;
        tau = 75; wff = 50; gseed = 0; verbose = 0; n_meta = 0;
        if ($value$plusargs("META_TAU_FF=%d", tau)) ;
        if ($value$plusargs("META_FFW=%d", wff)) ;
        if ($value$plusargs("META_SEED=%d", gseed)) ;
        if ($value$plusargs("META_VERBOSE=%d", verbose)) ;
        seed = SEED * 6151 + gseed * 98317 + 29;
        tsu = (TSU > 0) ? TSU : wff / 2;
        thd = (THD > 0) ? THD : wff / 2;
        ap = tsu + thd;
        c0 = (thd - tsu) / 2;           // aperture centre, ps after CK
        d_last = 1'bx; ce_last = 1'bx;
    end
    time t_ck = 0, t_in = 0;

    task resolve(input integer xoff, input reg vnew, input reg vold, input integer is_hold);
        begin
            noise = $dist_normal(seed, 0, (ap > 4) ? ap / 4 : 1);
            delta = c0 - xoff + noise;      // > 0: input early enough -> new
            choose = (delta > 0) ? vnew : vold;
            ad = (delta < 0) ? -delta : delta;
            if (ad < 1) ad = 1;
            if (2 * ad < ap) begin
                trr = tau * $ln((1.0 * ap) / (2.0 * ad));
                trp = (trr > 40.0 * tau) ? 40 * tau : $rtoi(trr);
            end else trp = 0;
            n_meta = n_meta + 1;
            if (verbose)
                $display("FFMETA %m t=%0t off=%0d delta=%0d -> %b after +%0d ps%s",
                         $time, xoff, delta, choose, trp, is_hold ? " (hold)" : "");
            if (!is_hold || delta > 0) Q <= #(TCKQ + trp) choose;
        end
    endtask

    always @(posedge CK) begin
        if (SR === 1'b1) Q <= #(TCKQ) SRVAL;
        else if (t_in > 0 && $time - t_in < tsu)
            resolve(-($time - t_in), CE ? D : Q, ce_last ? d_last : Q, 0);
        else if (CE) Q <= #(TCKQ) D;
        t_ck = $time;
    end

    always @(D or CE) begin
        if (t_ck > 0 && $time - t_ck < thd && SR !== 1'b1)
            resolve($time - t_ck, CE ? D : Q, Q, 1);
        t_in = $time;
    end
    // the values before the latest change, for the setup-side "old" choice
    reg d_now = 1'bx, ce_now = 1'bx;
    always @(D or CE) begin
        d_last = d_now; ce_last = ce_now;
        d_now = D; ce_now = CE;
    end

    // No specify path: iverilog's module path would schedule Q at
    // max(CK + TCKQ, resolution) instead of CK + TCKQ + resolution, i.e.
    // hide every resolution shorter than TCKQ.  Transport CK->Q instead.
endmodule
`endif

// ---- SLICE_LATX ---------------------------------------- LDCE and LDPE --
// A slice storage element in LATCH mode (nextpnr: SLICE_FFX with X_ORIG_TYPE
// LDCE/LDPE).  Transparent while CK == GHIGH and CE (the gate enable) is 1;
// SR is ASYNCHRONOUS and wins: Q = SRVAL (0 for LDCE's CLR, 1 for LDPE's PRE).
// GHIGH comes from IS_CLK_INVERTED (gen.py) or the slice's CLKINV bit
// (fasm2net.py): a latch-mode element is open while its post-CLKINV clock is
// low.  nextpnr's SDF has only CK->Q for this bel; D->Q while open and SR->Q
// take the same number, an assumption, stated.
module SLICE_LATX (
    input  wire CK, D, CE, SR,
    output wire Q
);
    parameter [0:0] INIT  = 1'b0;
    parameter [0:0] SRVAL = 1'b0;
    parameter [0:0] GHIGH = 1'b1;
    parameter TCKQ = 100;
    reg q;
    initial q = INIT;
    always @* begin
        if (SR === 1'b1)                     q = SRVAL;
        else if (SR !== 1'b0)                q = 1'bx;
        else if (CK === GHIGH && CE === 1'b1) q = D;
        else if ((CK !== GHIGH && CK !== ~GHIGH) || CE === 1'bx)
                                             q = (q === D) ? q : 1'bx;
    end
    assign Q = q;
    specify
        (CK => Q) = TCKQ; (D => Q) = TCKQ; (SR => Q) = TCKQ; (CE => Q) = TCKQ;
    endspecify
endmodule

// ---- CARRY4 ------------------------------------------------------- 1 bel --
// Flat scalar bel ports (not UNISIM's buses).  The SDF annotates only the
// S*/CIN arcs; the DI* arcs it omits keep the nominal below.
module CARRY4 (
    input  wire CIN, CYINIT,
    input  wire DI0, DI1, DI2, DI3,
    input  wire S0, S1, S2, S3,
    output wire O0, O1, O2, O3,
    output wire CO0, CO1, CO2, CO3
);
    wire cin0 = CIN | CYINIT;
    assign CO0 = S0 ? cin0 : DI0;
    assign CO1 = S1 ? CO0  : DI1;
    assign CO2 = S2 ? CO1  : DI2;
    assign CO3 = S3 ? CO2  : DI3;
    assign O0  = S0 ^ cin0;
    assign O1  = S1 ^ CO0;
    assign O2  = S2 ^ CO1;
    assign O3  = S3 ^ CO2;

    parameter TCINCO0=271, TCINCO1=157, TCINCO2=228, TCINCO3=114;
    parameter TCINO0=222, TCINO1=334, TCINO2=239, TCINO3=313;
    parameter TCYINITCO0=271, TCYINITCO1=157, TCYINITCO2=228, TCYINITCO3=114;
    parameter TCYINITO0=222, TCYINITO1=334, TCYINITO2=239, TCYINITO3=313;
    parameter TDI0CO0=100, TDI0CO1=100, TDI0CO2=100, TDI0CO3=100;
    parameter TDI0O1=100, TDI0O2=100, TDI0O3=100, TDI1CO1=100;
    parameter TDI1CO2=100, TDI1CO3=100, TDI1O2=100, TDI1O3=100;
    parameter TDI2CO2=100, TDI2CO3=100, TDI2O3=100, TDI3CO3=100;
    parameter TS0CO0=340, TS0CO1=433, TS0CO2=514, TS0CO3=489;
    parameter TS0O0=223, TS0O1=400, TS0O2=520, TS0O3=584;
    parameter TS1CO1=469, TS1CO2=558, TS1CO3=513, TS1O1=205;
    parameter TS1O2=558, TS1O3=623, TS2CO2=296, TS2CO3=358;
    parameter TS2O2=228, TS2O3=330, TS3CO3=354, TS3O3=233;
    specify
        (CIN => CO0) = TCINCO0; (CIN => CO1) = TCINCO1; (CIN => CO2) = TCINCO2; (CIN => CO3) = TCINCO3;
        (CIN => O0) = TCINO0; (CIN => O1) = TCINO1; (CIN => O2) = TCINO2; (CIN => O3) = TCINO3;
        (CYINIT => CO0) = TCYINITCO0; (CYINIT => CO1) = TCYINITCO1; (CYINIT => CO2) = TCYINITCO2; (CYINIT => CO3) = TCYINITCO3;
        (CYINIT => O0) = TCYINITO0; (CYINIT => O1) = TCYINITO1; (CYINIT => O2) = TCYINITO2; (CYINIT => O3) = TCYINITO3;
        (DI0 => CO0) = TDI0CO0; (DI0 => CO1) = TDI0CO1; (DI0 => CO2) = TDI0CO2; (DI0 => CO3) = TDI0CO3;
        (DI0 => O1) = TDI0O1; (DI0 => O2) = TDI0O2; (DI0 => O3) = TDI0O3; (DI1 => CO1) = TDI1CO1;
        (DI1 => CO2) = TDI1CO2; (DI1 => CO3) = TDI1CO3; (DI1 => O2) = TDI1O2; (DI1 => O3) = TDI1O3;
        (DI2 => CO2) = TDI2CO2; (DI2 => CO3) = TDI2CO3; (DI2 => O3) = TDI2O3; (DI3 => CO3) = TDI3CO3;
        (S0 => CO0) = TS0CO0; (S0 => CO1) = TS0CO1; (S0 => CO2) = TS0CO2; (S0 => CO3) = TS0CO3;
        (S0 => O0) = TS0O0; (S0 => O1) = TS0O1; (S0 => O2) = TS0O2; (S0 => O3) = TS0O3;
        (S1 => CO1) = TS1CO1; (S1 => CO2) = TS1CO2; (S1 => CO3) = TS1CO3; (S1 => O1) = TS1O1;
        (S1 => O2) = TS1O2; (S1 => O3) = TS1O3; (S2 => CO2) = TS2CO2; (S2 => CO3) = TS2CO3;
        (S2 => O2) = TS2O2; (S2 => O3) = TS2O3; (S3 => CO3) = TS3CO3; (S3 => O3) = TS3O3;
    endspecify
endmodule

// ---- DSP48E1_DSP48E1 ----------------------------------------- DSP48E1 --
// ONE configuration, the one this flow emits for a combinational multiply
// (yosys's 32x32 -> three cascaded DSPs, every pipeline register off):
// INMODE=0, ALUMODE=0, CARRYINSEL=0, CARRYIN=0, OPMODE[3:0]=0101 (X=Y=M),
// and OPMODE[6:4] (Z) one of 000 (head), 101 (PCIN>>>17, middle), 001 (PCIN,
// tail).  gen.py decodes the routed cell's control pins -- connected
// constant nets, DSP_VCC_PINS/DSP_GND_PINS tile constants, each XOR its
// IS_*_INVERTED parameter -- and REFUSES any cell outside this set (any *REG
// on, another OPMODE/ALUMODE/INMODE, a dynamic control pin, a connected
// output other than P/PCOUT/ACOUT), so nothing here is modelled by guess.
// The control pins are ports only so that their SDF arcs have a module path
// to land on; the function reads ZMUX/ACASC, which gen.py set from them.
//
//   A_USED = ACASC ? ACIN : A          (A_INPUT CASCADE / DIRECT, ACASCREG=0)
//   M      = signed(A_USED[24:0]) * signed(B[17:0])    43 bits, sign-extended
//   Z      = 0 | PCIN | PCIN>>>17      (ZMUX 0 / 1 / 5)
//   P = PCOUT = Z + M ;  ACOUT = A_USED
//
// The SDF gives every input bit an arc to every output bit and, on this
// chipdb, one value per (input group, output group) pair, so timing is one
// parameter per group pair (T<in>_<out>) on a full-connection path: the
// annotated build gets each per-bit IOPATH from the SDF (iverilog matches
// them pair by pair), the baked build the same numbers as parameters.
// `GLS_DSP_FAULT=<k>` flips P[k] and PCOUT[k]: the negative control.
module DSP48E1_DSP48E1 (
    input  wire A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29,
    input  wire ACIN0, ACIN1, ACIN2, ACIN3, ACIN4, ACIN5, ACIN6, ACIN7, ACIN8, ACIN9, ACIN10, ACIN11, ACIN12, ACIN13, ACIN14, ACIN15, ACIN16, ACIN17, ACIN18, ACIN19, ACIN20, ACIN21, ACIN22, ACIN23, ACIN24, ACIN25, ACIN26, ACIN27, ACIN28, ACIN29,
    input  wire B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17,
    input  wire C0, C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17, C18, C19, C20, C21, C22, C23, C24, C25, C26, C27, C28, C29, C30, C31, C32, C33, C34, C35, C36, C37, C38, C39, C40, C41, C42, C43, C44, C45, C46, C47,
    input  wire PCIN0, PCIN1, PCIN2, PCIN3, PCIN4, PCIN5, PCIN6, PCIN7, PCIN8, PCIN9, PCIN10, PCIN11, PCIN12, PCIN13, PCIN14, PCIN15, PCIN16, PCIN17, PCIN18, PCIN19, PCIN20, PCIN21, PCIN22, PCIN23, PCIN24, PCIN25, PCIN26, PCIN27, PCIN28, PCIN29, PCIN30, PCIN31, PCIN32, PCIN33, PCIN34, PCIN35, PCIN36, PCIN37, PCIN38, PCIN39, PCIN40, PCIN41, PCIN42, PCIN43, PCIN44, PCIN45, PCIN46, PCIN47,
    input  wire OPMODE0, OPMODE1, OPMODE2, OPMODE3, OPMODE4, OPMODE5, OPMODE6,
    input  wire ALUMODE0, ALUMODE1, ALUMODE2, ALUMODE3,
    input  wire CARRYINSEL0, CARRYINSEL1, CARRYINSEL2,
    input  wire CARRYIN,
    output wire P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, P28, P29, P30, P31, P32, P33, P34, P35, P36, P37, P38, P39, P40, P41, P42, P43, P44, P45, P46, P47,
    output wire PCOUT0, PCOUT1, PCOUT2, PCOUT3, PCOUT4, PCOUT5, PCOUT6, PCOUT7, PCOUT8, PCOUT9, PCOUT10, PCOUT11, PCOUT12, PCOUT13, PCOUT14, PCOUT15, PCOUT16, PCOUT17, PCOUT18, PCOUT19, PCOUT20, PCOUT21, PCOUT22, PCOUT23, PCOUT24, PCOUT25, PCOUT26, PCOUT27, PCOUT28, PCOUT29, PCOUT30, PCOUT31, PCOUT32, PCOUT33, PCOUT34, PCOUT35, PCOUT36, PCOUT37, PCOUT38, PCOUT39, PCOUT40, PCOUT41, PCOUT42, PCOUT43, PCOUT44, PCOUT45, PCOUT46, PCOUT47,
    output wire ACOUT0, ACOUT1, ACOUT2, ACOUT3, ACOUT4, ACOUT5, ACOUT6, ACOUT7, ACOUT8, ACOUT9, ACOUT10, ACOUT11, ACOUT12, ACOUT13, ACOUT14, ACOUT15, ACOUT16, ACOUT17, ACOUT18, ACOUT19, ACOUT20, ACOUT21, ACOUT22, ACOUT23, ACOUT24, ACOUT25, ACOUT26, ACOUT27, ACOUT28, ACOUT29
);
    parameter integer ZMUX = 0;
    parameter integer ACASC = 0;
    parameter TA_P=1000, TA_PCOUT=1000, TA_ACOUT=1000, TACIN_P=1000, TACIN_PCOUT=1000, TACIN_ACOUT=1000, TB_P=1000, TB_PCOUT=1000, TB_ACOUT=1000, TC_P=1000, TC_PCOUT=1000, TC_ACOUT=1000, TPCIN_P=1000, TPCIN_PCOUT=1000, TPCIN_ACOUT=1000, TOPMODE_P=1000, TOPMODE_PCOUT=1000, TOPMODE_ACOUT=1000, TALUMODE_P=1000, TALUMODE_PCOUT=1000, TALUMODE_ACOUT=1000, TCARRYINSEL_P=1000, TCARRYINSEL_PCOUT=1000, TCARRYINSEL_ACOUT=1000, TCARRYIN_P=1000, TCARRYIN_PCOUT=1000, TCARRYIN_ACOUT=1000;
    wire [29:0] a_in = {A29, A28, A27, A26, A25, A24, A23, A22, A21, A20, A19, A18, A17, A16, A15, A14, A13, A12, A11, A10, A9, A8, A7, A6, A5, A4, A3, A2, A1, A0};
    wire [29:0] acin = {ACIN29, ACIN28, ACIN27, ACIN26, ACIN25, ACIN24, ACIN23, ACIN22, ACIN21, ACIN20, ACIN19, ACIN18, ACIN17, ACIN16, ACIN15, ACIN14, ACIN13, ACIN12, ACIN11, ACIN10, ACIN9, ACIN8, ACIN7, ACIN6, ACIN5, ACIN4, ACIN3, ACIN2, ACIN1, ACIN0};
    wire [17:0] b_in = {B17, B16, B15, B14, B13, B12, B11, B10, B9, B8, B7, B6, B5, B4, B3, B2, B1, B0};
    wire [47:0] pcin = {PCIN47, PCIN46, PCIN45, PCIN44, PCIN43, PCIN42, PCIN41, PCIN40, PCIN39, PCIN38, PCIN37, PCIN36, PCIN35, PCIN34, PCIN33, PCIN32, PCIN31, PCIN30, PCIN29, PCIN28, PCIN27, PCIN26, PCIN25, PCIN24, PCIN23, PCIN22, PCIN21, PCIN20, PCIN19, PCIN18, PCIN17, PCIN16, PCIN15, PCIN14, PCIN13, PCIN12, PCIN11, PCIN10, PCIN9, PCIN8, PCIN7, PCIN6, PCIN5, PCIN4, PCIN3, PCIN2, PCIN1, PCIN0};
    wire [29:0] a_used = ACASC ? acin : a_in;
    wire signed [24:0] ma = a_used[24:0];
    wire signed [17:0] mb = b_in;
    wire signed [42:0] m  = ma * mb;
    wire [47:0] z = (ZMUX == 1) ? pcin
                  : (ZMUX == 5) ? {{17{pcin[47]}}, pcin[47:17]}
                  : 48'd0;
`ifdef GLS_DSP_FAULT
    wire [47:0] p = (z + {{5{m[42]}}, m}) ^ (48'd1 << `GLS_DSP_FAULT);
`else
    wire [47:0] p = z + {{5{m[42]}}, m};
`endif
    assign {P47, P46, P45, P44, P43, P42, P41, P40, P39, P38, P37, P36, P35, P34, P33, P32, P31, P30, P29, P28, P27, P26, P25, P24, P23, P22, P21, P20, P19, P18, P17, P16, P15, P14, P13, P12, P11, P10, P9, P8, P7, P6, P5, P4, P3, P2, P1, P0} = p;
    assign {PCOUT47, PCOUT46, PCOUT45, PCOUT44, PCOUT43, PCOUT42, PCOUT41, PCOUT40, PCOUT39, PCOUT38, PCOUT37, PCOUT36, PCOUT35, PCOUT34, PCOUT33, PCOUT32, PCOUT31, PCOUT30, PCOUT29, PCOUT28, PCOUT27, PCOUT26, PCOUT25, PCOUT24, PCOUT23, PCOUT22, PCOUT21, PCOUT20, PCOUT19, PCOUT18, PCOUT17, PCOUT16, PCOUT15, PCOUT14, PCOUT13, PCOUT12, PCOUT11, PCOUT10, PCOUT9, PCOUT8, PCOUT7, PCOUT6, PCOUT5, PCOUT4, PCOUT3, PCOUT2, PCOUT1, PCOUT0} = p;
    assign {ACOUT29, ACOUT28, ACOUT27, ACOUT26, ACOUT25, ACOUT24, ACOUT23, ACOUT22, ACOUT21, ACOUT20, ACOUT19, ACOUT18, ACOUT17, ACOUT16, ACOUT15, ACOUT14, ACOUT13, ACOUT12, ACOUT11, ACOUT10, ACOUT9, ACOUT8, ACOUT7, ACOUT6, ACOUT5, ACOUT4, ACOUT3, ACOUT2, ACOUT1, ACOUT0} = a_used;
    specify
        (A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29 *> P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, P28, P29, P30, P31, P32, P33, P34, P35, P36, P37, P38, P39, P40, P41, P42, P43, P44, P45, P46, P47) = TA_P;
        (A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29 *> PCOUT0, PCOUT1, PCOUT2, PCOUT3, PCOUT4, PCOUT5, PCOUT6, PCOUT7, PCOUT8, PCOUT9, PCOUT10, PCOUT11, PCOUT12, PCOUT13, PCOUT14, PCOUT15, PCOUT16, PCOUT17, PCOUT18, PCOUT19, PCOUT20, PCOUT21, PCOUT22, PCOUT23, PCOUT24, PCOUT25, PCOUT26, PCOUT27, PCOUT28, PCOUT29, PCOUT30, PCOUT31, PCOUT32, PCOUT33, PCOUT34, PCOUT35, PCOUT36, PCOUT37, PCOUT38, PCOUT39, PCOUT40, PCOUT41, PCOUT42, PCOUT43, PCOUT44, PCOUT45, PCOUT46, PCOUT47) = TA_PCOUT;
        (A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29 *> ACOUT0, ACOUT1, ACOUT2, ACOUT3, ACOUT4, ACOUT5, ACOUT6, ACOUT7, ACOUT8, ACOUT9, ACOUT10, ACOUT11, ACOUT12, ACOUT13, ACOUT14, ACOUT15, ACOUT16, ACOUT17, ACOUT18, ACOUT19, ACOUT20, ACOUT21, ACOUT22, ACOUT23, ACOUT24, ACOUT25, ACOUT26, ACOUT27, ACOUT28, ACOUT29) = TA_ACOUT;
        (ACIN0, ACIN1, ACIN2, ACIN3, ACIN4, ACIN5, ACIN6, ACIN7, ACIN8, ACIN9, ACIN10, ACIN11, ACIN12, ACIN13, ACIN14, ACIN15, ACIN16, ACIN17, ACIN18, ACIN19, ACIN20, ACIN21, ACIN22, ACIN23, ACIN24, ACIN25, ACIN26, ACIN27, ACIN28, ACIN29 *> P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, P28, P29, P30, P31, P32, P33, P34, P35, P36, P37, P38, P39, P40, P41, P42, P43, P44, P45, P46, P47) = TACIN_P;
        (ACIN0, ACIN1, ACIN2, ACIN3, ACIN4, ACIN5, ACIN6, ACIN7, ACIN8, ACIN9, ACIN10, ACIN11, ACIN12, ACIN13, ACIN14, ACIN15, ACIN16, ACIN17, ACIN18, ACIN19, ACIN20, ACIN21, ACIN22, ACIN23, ACIN24, ACIN25, ACIN26, ACIN27, ACIN28, ACIN29 *> PCOUT0, PCOUT1, PCOUT2, PCOUT3, PCOUT4, PCOUT5, PCOUT6, PCOUT7, PCOUT8, PCOUT9, PCOUT10, PCOUT11, PCOUT12, PCOUT13, PCOUT14, PCOUT15, PCOUT16, PCOUT17, PCOUT18, PCOUT19, PCOUT20, PCOUT21, PCOUT22, PCOUT23, PCOUT24, PCOUT25, PCOUT26, PCOUT27, PCOUT28, PCOUT29, PCOUT30, PCOUT31, PCOUT32, PCOUT33, PCOUT34, PCOUT35, PCOUT36, PCOUT37, PCOUT38, PCOUT39, PCOUT40, PCOUT41, PCOUT42, PCOUT43, PCOUT44, PCOUT45, PCOUT46, PCOUT47) = TACIN_PCOUT;
        (ACIN0, ACIN1, ACIN2, ACIN3, ACIN4, ACIN5, ACIN6, ACIN7, ACIN8, ACIN9, ACIN10, ACIN11, ACIN12, ACIN13, ACIN14, ACIN15, ACIN16, ACIN17, ACIN18, ACIN19, ACIN20, ACIN21, ACIN22, ACIN23, ACIN24, ACIN25, ACIN26, ACIN27, ACIN28, ACIN29 *> ACOUT0, ACOUT1, ACOUT2, ACOUT3, ACOUT4, ACOUT5, ACOUT6, ACOUT7, ACOUT8, ACOUT9, ACOUT10, ACOUT11, ACOUT12, ACOUT13, ACOUT14, ACOUT15, ACOUT16, ACOUT17, ACOUT18, ACOUT19, ACOUT20, ACOUT21, ACOUT22, ACOUT23, ACOUT24, ACOUT25, ACOUT26, ACOUT27, ACOUT28, ACOUT29) = TACIN_ACOUT;
        (B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17 *> P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, P28, P29, P30, P31, P32, P33, P34, P35, P36, P37, P38, P39, P40, P41, P42, P43, P44, P45, P46, P47) = TB_P;
        (B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17 *> PCOUT0, PCOUT1, PCOUT2, PCOUT3, PCOUT4, PCOUT5, PCOUT6, PCOUT7, PCOUT8, PCOUT9, PCOUT10, PCOUT11, PCOUT12, PCOUT13, PCOUT14, PCOUT15, PCOUT16, PCOUT17, PCOUT18, PCOUT19, PCOUT20, PCOUT21, PCOUT22, PCOUT23, PCOUT24, PCOUT25, PCOUT26, PCOUT27, PCOUT28, PCOUT29, PCOUT30, PCOUT31, PCOUT32, PCOUT33, PCOUT34, PCOUT35, PCOUT36, PCOUT37, PCOUT38, PCOUT39, PCOUT40, PCOUT41, PCOUT42, PCOUT43, PCOUT44, PCOUT45, PCOUT46, PCOUT47) = TB_PCOUT;
        (B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17 *> ACOUT0, ACOUT1, ACOUT2, ACOUT3, ACOUT4, ACOUT5, ACOUT6, ACOUT7, ACOUT8, ACOUT9, ACOUT10, ACOUT11, ACOUT12, ACOUT13, ACOUT14, ACOUT15, ACOUT16, ACOUT17, ACOUT18, ACOUT19, ACOUT20, ACOUT21, ACOUT22, ACOUT23, ACOUT24, ACOUT25, ACOUT26, ACOUT27, ACOUT28, ACOUT29) = TB_ACOUT;
        (C0, C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17, C18, C19, C20, C21, C22, C23, C24, C25, C26, C27, C28, C29, C30, C31, C32, C33, C34, C35, C36, C37, C38, C39, C40, C41, C42, C43, C44, C45, C46, C47 *> P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, P28, P29, P30, P31, P32, P33, P34, P35, P36, P37, P38, P39, P40, P41, P42, P43, P44, P45, P46, P47) = TC_P;
        (C0, C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17, C18, C19, C20, C21, C22, C23, C24, C25, C26, C27, C28, C29, C30, C31, C32, C33, C34, C35, C36, C37, C38, C39, C40, C41, C42, C43, C44, C45, C46, C47 *> PCOUT0, PCOUT1, PCOUT2, PCOUT3, PCOUT4, PCOUT5, PCOUT6, PCOUT7, PCOUT8, PCOUT9, PCOUT10, PCOUT11, PCOUT12, PCOUT13, PCOUT14, PCOUT15, PCOUT16, PCOUT17, PCOUT18, PCOUT19, PCOUT20, PCOUT21, PCOUT22, PCOUT23, PCOUT24, PCOUT25, PCOUT26, PCOUT27, PCOUT28, PCOUT29, PCOUT30, PCOUT31, PCOUT32, PCOUT33, PCOUT34, PCOUT35, PCOUT36, PCOUT37, PCOUT38, PCOUT39, PCOUT40, PCOUT41, PCOUT42, PCOUT43, PCOUT44, PCOUT45, PCOUT46, PCOUT47) = TC_PCOUT;
        (C0, C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17, C18, C19, C20, C21, C22, C23, C24, C25, C26, C27, C28, C29, C30, C31, C32, C33, C34, C35, C36, C37, C38, C39, C40, C41, C42, C43, C44, C45, C46, C47 *> ACOUT0, ACOUT1, ACOUT2, ACOUT3, ACOUT4, ACOUT5, ACOUT6, ACOUT7, ACOUT8, ACOUT9, ACOUT10, ACOUT11, ACOUT12, ACOUT13, ACOUT14, ACOUT15, ACOUT16, ACOUT17, ACOUT18, ACOUT19, ACOUT20, ACOUT21, ACOUT22, ACOUT23, ACOUT24, ACOUT25, ACOUT26, ACOUT27, ACOUT28, ACOUT29) = TC_ACOUT;
        (PCIN0, PCIN1, PCIN2, PCIN3, PCIN4, PCIN5, PCIN6, PCIN7, PCIN8, PCIN9, PCIN10, PCIN11, PCIN12, PCIN13, PCIN14, PCIN15, PCIN16, PCIN17, PCIN18, PCIN19, PCIN20, PCIN21, PCIN22, PCIN23, PCIN24, PCIN25, PCIN26, PCIN27, PCIN28, PCIN29, PCIN30, PCIN31, PCIN32, PCIN33, PCIN34, PCIN35, PCIN36, PCIN37, PCIN38, PCIN39, PCIN40, PCIN41, PCIN42, PCIN43, PCIN44, PCIN45, PCIN46, PCIN47 *> P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, P28, P29, P30, P31, P32, P33, P34, P35, P36, P37, P38, P39, P40, P41, P42, P43, P44, P45, P46, P47) = TPCIN_P;
        (PCIN0, PCIN1, PCIN2, PCIN3, PCIN4, PCIN5, PCIN6, PCIN7, PCIN8, PCIN9, PCIN10, PCIN11, PCIN12, PCIN13, PCIN14, PCIN15, PCIN16, PCIN17, PCIN18, PCIN19, PCIN20, PCIN21, PCIN22, PCIN23, PCIN24, PCIN25, PCIN26, PCIN27, PCIN28, PCIN29, PCIN30, PCIN31, PCIN32, PCIN33, PCIN34, PCIN35, PCIN36, PCIN37, PCIN38, PCIN39, PCIN40, PCIN41, PCIN42, PCIN43, PCIN44, PCIN45, PCIN46, PCIN47 *> PCOUT0, PCOUT1, PCOUT2, PCOUT3, PCOUT4, PCOUT5, PCOUT6, PCOUT7, PCOUT8, PCOUT9, PCOUT10, PCOUT11, PCOUT12, PCOUT13, PCOUT14, PCOUT15, PCOUT16, PCOUT17, PCOUT18, PCOUT19, PCOUT20, PCOUT21, PCOUT22, PCOUT23, PCOUT24, PCOUT25, PCOUT26, PCOUT27, PCOUT28, PCOUT29, PCOUT30, PCOUT31, PCOUT32, PCOUT33, PCOUT34, PCOUT35, PCOUT36, PCOUT37, PCOUT38, PCOUT39, PCOUT40, PCOUT41, PCOUT42, PCOUT43, PCOUT44, PCOUT45, PCOUT46, PCOUT47) = TPCIN_PCOUT;
        (PCIN0, PCIN1, PCIN2, PCIN3, PCIN4, PCIN5, PCIN6, PCIN7, PCIN8, PCIN9, PCIN10, PCIN11, PCIN12, PCIN13, PCIN14, PCIN15, PCIN16, PCIN17, PCIN18, PCIN19, PCIN20, PCIN21, PCIN22, PCIN23, PCIN24, PCIN25, PCIN26, PCIN27, PCIN28, PCIN29, PCIN30, PCIN31, PCIN32, PCIN33, PCIN34, PCIN35, PCIN36, PCIN37, PCIN38, PCIN39, PCIN40, PCIN41, PCIN42, PCIN43, PCIN44, PCIN45, PCIN46, PCIN47 *> ACOUT0, ACOUT1, ACOUT2, ACOUT3, ACOUT4, ACOUT5, ACOUT6, ACOUT7, ACOUT8, ACOUT9, ACOUT10, ACOUT11, ACOUT12, ACOUT13, ACOUT14, ACOUT15, ACOUT16, ACOUT17, ACOUT18, ACOUT19, ACOUT20, ACOUT21, ACOUT22, ACOUT23, ACOUT24, ACOUT25, ACOUT26, ACOUT27, ACOUT28, ACOUT29) = TPCIN_ACOUT;
        (OPMODE0, OPMODE1, OPMODE2, OPMODE3, OPMODE4, OPMODE5, OPMODE6 *> P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, P28, P29, P30, P31, P32, P33, P34, P35, P36, P37, P38, P39, P40, P41, P42, P43, P44, P45, P46, P47) = TOPMODE_P;
        (OPMODE0, OPMODE1, OPMODE2, OPMODE3, OPMODE4, OPMODE5, OPMODE6 *> PCOUT0, PCOUT1, PCOUT2, PCOUT3, PCOUT4, PCOUT5, PCOUT6, PCOUT7, PCOUT8, PCOUT9, PCOUT10, PCOUT11, PCOUT12, PCOUT13, PCOUT14, PCOUT15, PCOUT16, PCOUT17, PCOUT18, PCOUT19, PCOUT20, PCOUT21, PCOUT22, PCOUT23, PCOUT24, PCOUT25, PCOUT26, PCOUT27, PCOUT28, PCOUT29, PCOUT30, PCOUT31, PCOUT32, PCOUT33, PCOUT34, PCOUT35, PCOUT36, PCOUT37, PCOUT38, PCOUT39, PCOUT40, PCOUT41, PCOUT42, PCOUT43, PCOUT44, PCOUT45, PCOUT46, PCOUT47) = TOPMODE_PCOUT;
        (OPMODE0, OPMODE1, OPMODE2, OPMODE3, OPMODE4, OPMODE5, OPMODE6 *> ACOUT0, ACOUT1, ACOUT2, ACOUT3, ACOUT4, ACOUT5, ACOUT6, ACOUT7, ACOUT8, ACOUT9, ACOUT10, ACOUT11, ACOUT12, ACOUT13, ACOUT14, ACOUT15, ACOUT16, ACOUT17, ACOUT18, ACOUT19, ACOUT20, ACOUT21, ACOUT22, ACOUT23, ACOUT24, ACOUT25, ACOUT26, ACOUT27, ACOUT28, ACOUT29) = TOPMODE_ACOUT;
        (ALUMODE0, ALUMODE1, ALUMODE2, ALUMODE3 *> P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, P28, P29, P30, P31, P32, P33, P34, P35, P36, P37, P38, P39, P40, P41, P42, P43, P44, P45, P46, P47) = TALUMODE_P;
        (ALUMODE0, ALUMODE1, ALUMODE2, ALUMODE3 *> PCOUT0, PCOUT1, PCOUT2, PCOUT3, PCOUT4, PCOUT5, PCOUT6, PCOUT7, PCOUT8, PCOUT9, PCOUT10, PCOUT11, PCOUT12, PCOUT13, PCOUT14, PCOUT15, PCOUT16, PCOUT17, PCOUT18, PCOUT19, PCOUT20, PCOUT21, PCOUT22, PCOUT23, PCOUT24, PCOUT25, PCOUT26, PCOUT27, PCOUT28, PCOUT29, PCOUT30, PCOUT31, PCOUT32, PCOUT33, PCOUT34, PCOUT35, PCOUT36, PCOUT37, PCOUT38, PCOUT39, PCOUT40, PCOUT41, PCOUT42, PCOUT43, PCOUT44, PCOUT45, PCOUT46, PCOUT47) = TALUMODE_PCOUT;
        (ALUMODE0, ALUMODE1, ALUMODE2, ALUMODE3 *> ACOUT0, ACOUT1, ACOUT2, ACOUT3, ACOUT4, ACOUT5, ACOUT6, ACOUT7, ACOUT8, ACOUT9, ACOUT10, ACOUT11, ACOUT12, ACOUT13, ACOUT14, ACOUT15, ACOUT16, ACOUT17, ACOUT18, ACOUT19, ACOUT20, ACOUT21, ACOUT22, ACOUT23, ACOUT24, ACOUT25, ACOUT26, ACOUT27, ACOUT28, ACOUT29) = TALUMODE_ACOUT;
        (CARRYINSEL0, CARRYINSEL1, CARRYINSEL2 *> P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, P28, P29, P30, P31, P32, P33, P34, P35, P36, P37, P38, P39, P40, P41, P42, P43, P44, P45, P46, P47) = TCARRYINSEL_P;
        (CARRYINSEL0, CARRYINSEL1, CARRYINSEL2 *> PCOUT0, PCOUT1, PCOUT2, PCOUT3, PCOUT4, PCOUT5, PCOUT6, PCOUT7, PCOUT8, PCOUT9, PCOUT10, PCOUT11, PCOUT12, PCOUT13, PCOUT14, PCOUT15, PCOUT16, PCOUT17, PCOUT18, PCOUT19, PCOUT20, PCOUT21, PCOUT22, PCOUT23, PCOUT24, PCOUT25, PCOUT26, PCOUT27, PCOUT28, PCOUT29, PCOUT30, PCOUT31, PCOUT32, PCOUT33, PCOUT34, PCOUT35, PCOUT36, PCOUT37, PCOUT38, PCOUT39, PCOUT40, PCOUT41, PCOUT42, PCOUT43, PCOUT44, PCOUT45, PCOUT46, PCOUT47) = TCARRYINSEL_PCOUT;
        (CARRYINSEL0, CARRYINSEL1, CARRYINSEL2 *> ACOUT0, ACOUT1, ACOUT2, ACOUT3, ACOUT4, ACOUT5, ACOUT6, ACOUT7, ACOUT8, ACOUT9, ACOUT10, ACOUT11, ACOUT12, ACOUT13, ACOUT14, ACOUT15, ACOUT16, ACOUT17, ACOUT18, ACOUT19, ACOUT20, ACOUT21, ACOUT22, ACOUT23, ACOUT24, ACOUT25, ACOUT26, ACOUT27, ACOUT28, ACOUT29) = TCARRYINSEL_ACOUT;
        (CARRYIN *> P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, P28, P29, P30, P31, P32, P33, P34, P35, P36, P37, P38, P39, P40, P41, P42, P43, P44, P45, P46, P47) = TCARRYIN_P;
        (CARRYIN *> PCOUT0, PCOUT1, PCOUT2, PCOUT3, PCOUT4, PCOUT5, PCOUT6, PCOUT7, PCOUT8, PCOUT9, PCOUT10, PCOUT11, PCOUT12, PCOUT13, PCOUT14, PCOUT15, PCOUT16, PCOUT17, PCOUT18, PCOUT19, PCOUT20, PCOUT21, PCOUT22, PCOUT23, PCOUT24, PCOUT25, PCOUT26, PCOUT27, PCOUT28, PCOUT29, PCOUT30, PCOUT31, PCOUT32, PCOUT33, PCOUT34, PCOUT35, PCOUT36, PCOUT37, PCOUT38, PCOUT39, PCOUT40, PCOUT41, PCOUT42, PCOUT43, PCOUT44, PCOUT45, PCOUT46, PCOUT47) = TCARRYIN_PCOUT;
        (CARRYIN *> ACOUT0, ACOUT1, ACOUT2, ACOUT3, ACOUT4, ACOUT5, ACOUT6, ACOUT7, ACOUT8, ACOUT9, ACOUT10, ACOUT11, ACOUT12, ACOUT13, ACOUT14, ACOUT15, ACOUT16, ACOUT17, ACOUT18, ACOUT19, ACOUT20, ACOUT21, ACOUT22, ACOUT23, ACOUT24, ACOUT25, ACOUT26, ACOUT27, ACOUT28, ACOUT29) = TCARRYIN_ACOUT;
    endspecify
endmodule


// ---- BUFGCTRL -------------------------------------------------- BUFG bel --
// All three came from a plain BUFG (X_ORIG_TYPE), with IS_S1/IS_CE1/
// IS_IGNORE1_INVERTED set so the I1 half of the glitchless mux is permanently
// deselected.  Modelled as the buffer that configuration reduces to.
module BUFGCTRL (
    input  wire I0, I1, S0, S1, CE0, CE1, IGNORE0, IGNORE1,
    output wire O
);
    parameter TI0O = 200;
    assign O = I0;
    specify (I0 => O) = TI0O; endspecify
endmodule

// ---- BSCAN ------------------------------------------------------ BSCANE2 --
// Passive stub: SEL low, so the JTAG user-DR machine never activates, gcd_hw's
// hold register stays at its 12'h0 power-on value and the readback shifter
// never runs.  That is precisely the free-running, no-JTAG condition a
// software-driven sweep leaves the part in between scans.  The SDF carries no
// timing for this cell.
module BSCAN (
    input  wire TDO,
    output wire CAPTURE, DRCK, RESET, RUNTEST, SEL, SHIFT, TCK, TDI, TMS, UPDATE
);
    assign CAPTURE = 1'b0, DRCK = 1'b0, RESET = 1'b0, RUNTEST = 1'b0,
           SEL = 1'b0, SHIFT = 1'b0, TCK = 1'b0, TDI = 1'b0, TMS = 1'b0,
           UPDATE = 1'b0;
endmodule

// ---- pads ------------------------------------------------------------------
// No SDF timing for any of these.  PAD's port is an INTERCONNECT destination
// in this design (the OBUF drives it), so it is modelled as an input.
module PAD (input wire PAD);
endmodule

module IOB33_OUTBUF (input wire IN, output wire OUT);
    assign OUT = IN;
endmodule

module IOB33_INBUF_EN (input wire PAD, output wire OUT);
    assign OUT = PAD;
endmodule

module PSEUDO_GND (output wire Y); assign Y = 1'b0; endmodule
module PSEUDO_VCC (output wire Y); assign Y = 1'b1; endmodule

`default_nettype wire
