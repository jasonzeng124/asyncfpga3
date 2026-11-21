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
//        delta = p - CEN + N(0, WIN/4)        (thermal noise),
//    CEN = TLOOP*META_CENTRE_PM/1000 (default 500: TLOOP/2); META_CENTRE_PM<0: TLOOP - WIN/2
//      delta <= -WIN/2 : the runt is rejected (one runt reaches fanout; its echo is ignored);
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
    integer cpm, cen;   // +META_CENTRE_PM=: decision centre in per-mille of TLOOP (Fid3 proposal)
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
        cpm = 500;                              // TLOOP/2: the duty-balanced point of the
        if ($value$plusargs("META_CENTRE_PM=%d", cpm)) ;   // circulating runt (see A-fid3.md)
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
                cen = (cpm >= 0) ? (TLOOP * cpm) / 1000 : TLOOP - win / 2;   // cpm < 0: the old rule
                delta = p - cen + noise;
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
