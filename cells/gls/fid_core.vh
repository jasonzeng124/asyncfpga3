// ---------------------------------------------------------------------------
// fid_core.vh -- the opt-in "silicon-like" primitive core (F3).  Included by
// gls/prims.v under GLS_FID (sim/bd_prims_sim.v has no BD_FID path in the
// tree; see f3_model.md); nothing here is compiled into the default GLS.
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
//    +META_X=1).  The feedback pin is evaluated from the node's committed
//    state, not from the wire (FID_RESOLVE below), so a runt has no echo and
//    every other input change is evaluated when it arrives; only a change
//    during a resolution waits for the commit.  (Until this was fixed the
//    echo was masked by ignoring ALL changes for TLOOP after a runt, which
//    lost a genuine follow pulse: audit r16 follow_lost, tb_f3_follow.v.)
//    TAU/WIN for a LUT loop are not published anywhere found; defaults
//    TAU=WIN=150 ps are an assumption (see f3_model.md), plusargs
//    +META_TAU=, +META_WIN=, +META_SEED=, +META_VERBOSE=1, +META_OFF=1 (the
//    resolver disabled: pure transport, the ablation the negative controls use).
// ---------------------------------------------------------------------------

`ifndef FID_CORE_VH
`define FID_CORE_VH

// The state-node resolver.  f is the LUT function of the delayed pins as they
// are (used only when the resolver is off); f0 / f1 are the same function with
// the feedback pin(s) forced to 0 / 1.  With the resolver on, the feedback pin
// is not read off the wire but taken from the node's own committed state `fb`:
// an accepted edge reaches fb TLOOP after it (the same instant the routed
// feedback wire + pin arc would deliver it), a runt never does, and a
// metastable commit sets fb at once (the whole loop settles together).  So
// the loop's echo of a runt does not exist and nothing is ignored: every
// change of the other pins is evaluated when it arrives.  While the node is
// metastable (busy) it holds vhold; a change that drives it away from vhold
// to a 0/1 value ends the resolution and is an ordinary edge from vhold (the
// drive wins; counted in n_break).  Only a change to x waits for the commit
// (n_fold).  +META_VERBOSE=1 shows both.
module FID_RESOLVE (input wire f, input wire f0, input wire f1, input wire en,
                    output wire o);
    parameter integer TLOOP = 0;
    parameter integer SEED  = 1;
    parameter integer TAU   = 150;
    parameter integer WIN   = 150;
    integer tau, win, seed, gseed, verbose, xmode, off;
    integer n_meta, n_rej, n_commit, n_fold, n_break;
    reg o_r = 1'bx, fb = 1'bx;
    assign o = o_r;
    reg busy = 1'b0, pend = 1'b0, v_before = 1'bx, runt_val, choose, fv, vhold;
    time t_last = 0, p;
    integer noise, delta, ad, trp, kq = 0, kq_next = 0, kc = 0, kc_next = 0;
    real trr;
    wire on = (en === 1'b1) && (TLOOP != 0) && !off;
    wire fe = (fb === 1'b1) ? f1 : (fb === 1'b0) ? f0 : ((f0 === f1) ? f0 : 1'bx);
    initial begin
        tau = TAU; win = WIN; gseed = 0; verbose = 0; xmode = 0; off = 0;
        if ($value$plusargs("META_OFF=%d", off)) ;   // ablation: transport only
        n_meta = 0; n_rej = 0; n_commit = 0; n_fold = 0; n_break = 0;
        if ($value$plusargs("META_TAU=%d", tau)) ;
        if ($value$plusargs("META_WIN=%d", win)) ;
        if ($value$plusargs("META_SEED=%d", gseed)) ;
        if ($value$plusargs("META_VERBOSE=%d", verbose)) ;
        if ($value$plusargs("META_X=%d", xmode)) ;
        seed = SEED * 7919 + gseed * 104729 + 17;
    end
    always @(f) if (!on) o_r = f;

    // fe from the current fb (the wire above lags a procedural fb update by
    // one event, and the decision must not depend on event order)
    function fsel(input b, input g0, input g1);
        fsel = (b === 1'b1) ? g1 : (b === 1'b0) ? g0 : ((g0 === g1) ? g0 : 1'bx);
    endfunction
    task step;
        begin
        // an accepted edge whose loop delay is up now reaches fb first, so an
        // input change arriving at the same instant sees the new state (as the
        // transport loop does)
        if (pend && $time >= t_last + TLOOP) begin
            pend = 1'b0;
            fb = o_r;
        end
        fv = fsel(fb, f0, f1);
        if (busy && (fv === 1'b0 || fv === 1'b1) && fv !== vhold) begin
            n_break = n_break + 1;
            if (verbose)
                $display("BREAK %m t=%0t drive to %b ends the resolution", $time, fv);
            busy = 1'b0;
            kc_next = kc_next + 1;              // the pending commit is void
            v_before = vhold;
            o_r = fv;
            t_last = $time;
            pend = 1'b1;
            kq_next = kq_next + 1;
            kq <= #(TLOOP) kq_next;
        end else if (busy) begin
            if (fv !== vhold) begin
                n_fold = n_fold + 1;
                if (verbose)
                    $display("FOLD %m t=%0t x while resolving, evaluated at commit", $time);
            end
        end else if (fv !== o_r) begin
            if ((fv === 1'b0 || fv === 1'b1) && (o_r === 1'b0 || o_r === 1'b1)
                    && pend && fv === v_before && ($time - t_last) < TLOOP) begin
                p = $time - t_last;
                runt_val = o_r;
                pend = 1'b0;                    // the runt never reaches fb
                noise = $dist_normal(seed, 0, (win > 4) ? win / 4 : 1);
                delta = p - (TLOOP - win / 2) + noise;
                if (delta <= -(win / 2)) begin
                    n_rej = n_rej + 1;
                    if (verbose > 1)
                        $display("RUNT %m t=%0t runt=%0t loop=%0d rejected", $time, p, TLOOP);
                    o_r = fv;
                end else begin
                    choose = (delta > 0) ? runt_val : fv;
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
                    vhold = fv;
                    o_r = xmode ? 1'bx : fv;
                    busy = 1'b1;
                    kc_next = kc_next + 1;
                    kc <= #(trp) kc_next;
                end
            end else begin
                v_before = o_r;
                o_r = fv;
                t_last = $time;
                pend = 1'b1;
                kq_next = kq_next + 1;
                kq <= #(TLOOP) kq_next;
            end
        end
        end
    endtask

    always @(fe) if (on) step;
    // an accepted edge reaches the feedback pin TLOOP after it
    always @(kq) if (on) step;
    // a metastable node commits: output and loop settle together
    always @(kc) if (on && busy && kc == kc_next) begin
        busy = 1'b0;
        o_r = choose;
        fb = choose;
        step;
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
// resolver on for that output (static, from gen.py).  FB6/FB5 name the pins
// that output is routed back into (bit k-1 = pin Ak); the resolver needs them
// (it evaluates those pins from the node's committed state), so an enabled
// resolver without one is a hard error.
module FID_LUT6 (input wire A1, A2, A3, A4, A5, A6,
                 input wire EN6, EN5,
                 output wire O5, O6);
    parameter [63:0] INIT = 64'h0;
    parameter integer T1_6 = 124, T2_6 = 124, T3_6 = 124, T4_6 = 124, T5_6 = 124, T6_6 = 124;
    parameter integer T1_5 = 124, T2_5 = 124, T3_5 = 124, T4_5 = 124, T5_5 = 124;
    parameter integer TLOOP6 = 0, TLOOP5 = 0;
    parameter [5:0] FB6 = 6'b0;
    parameter [4:0] FB5 = 5'b0;
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
    // agree, whatever the order), so the root/leaf distinction lives in the
    // delays above.
    function m6(input [63:0] t, input s1, s2, s3, s4, s5, s6);
        reg [31:0] w5; reg [15:0] w4; reg [7:0] w3; reg [3:0] w2; reg [1:0] w1;
        begin
            w5 = s6 ? t[63:32] : t[31:0];
            w4 = s5 ? w5[31:16] : w5[15:0];
            w3 = s4 ? w4[15:8] : w4[7:0];
            w2 = s3 ? w3[7:4] : w3[3:0];
            w1 = s2 ? w2[3:2] : w2[1:0];
            m6 = s1 ? w1[1] : w1[0];
        end
    endfunction
    wire f6 = m6(INIT, a1, a2, a3, a4, a5, a6);
    wire f5 = m6({32'b0, INIT[31:0]}, b1, b2, b3, b4, b5, 1'b0);
    // the same with the feedback pin(s) forced to 0 / 1 (see FID_RESOLVE);
    // built only for an output that has a feedback pin
    wire f6_0, f6_1, f5_0, f5_1;
    generate if (FB6 != 0) begin : g_fb6
        assign f6_0 = m6(INIT, FB6[0] ? 1'b0 : a1, FB6[1] ? 1'b0 : a2, FB6[2] ? 1'b0 : a3,
                         FB6[3] ? 1'b0 : a4, FB6[4] ? 1'b0 : a5, FB6[5] ? 1'b0 : a6);
        assign f6_1 = m6(INIT, FB6[0] ? 1'b1 : a1, FB6[1] ? 1'b1 : a2, FB6[2] ? 1'b1 : a3,
                         FB6[3] ? 1'b1 : a4, FB6[4] ? 1'b1 : a5, FB6[5] ? 1'b1 : a6);
    end else begin : g_nofb6
        assign f6_0 = 1'b0; assign f6_1 = 1'b0;
    end endgenerate
    generate if (FB5 != 0) begin : g_fb5
        assign f5_0 = m6({32'b0, INIT[31:0]}, FB5[0] ? 1'b0 : b1, FB5[1] ? 1'b0 : b2,
                         FB5[2] ? 1'b0 : b3, FB5[3] ? 1'b0 : b4, FB5[4] ? 1'b0 : b5, 1'b0);
        assign f5_1 = m6({32'b0, INIT[31:0]}, FB5[0] ? 1'b1 : b1, FB5[1] ? 1'b1 : b2,
                         FB5[2] ? 1'b1 : b3, FB5[3] ? 1'b1 : b4, FB5[4] ? 1'b1 : b5, 1'b0);
    end else begin : g_nofb5
        assign f5_0 = 1'b0; assign f5_1 = 1'b0;
    end endgenerate
    initial #1 if ((EN6 === 1'b1 && TLOOP6 != 0 && FB6 == 0) || (EN5 === 1'b1 && TLOOP5 != 0 && FB5 == 0)) begin
        $display("FID_LUT6 %m: state resolver enabled without its feedback pin (FB6/FB5)");
        $finish;
    end

    // Two pins whose delayed copies land in the same time step update one
    // after the other, so f can glitch for zero time between them -- a
    // simulator artefact (it once fed the resolver a 0 ps "runt").  The
    // sampler takes f 1 ps after its first change, once per step.
    wire f6s, f5s, f6s0, f6s1, f5s0, f5s1;
    FID_SAMPLE s6 (.f(f6), .o(f6s));
    FID_SAMPLE s5 (.f(f5), .o(f5s));
    FID_SAMPLE s60 (.f(f6_0), .o(f6s0));
    FID_SAMPLE s61 (.f(f6_1), .o(f6s1));
    FID_SAMPLE s50 (.f(f5_0), .o(f5s0));
    FID_SAMPLE s51 (.f(f5_1), .o(f5s1));
    FID_RESOLVE #(.TLOOP(TLOOP6), .SEED(2 * SEED + 1)) r6 (.f(f6s), .f0(f6s0), .f1(f6s1), .en(EN6), .o(O6));
    FID_RESOLVE #(.TLOOP(TLOOP5), .SEED(2 * SEED))     r5 (.f(f5s), .f0(f5s0), .f1(f5s1), .en(EN5), .o(O5));
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
