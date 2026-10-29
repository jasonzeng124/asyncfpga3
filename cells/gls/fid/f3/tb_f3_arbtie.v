// tb_f3_arbtie.v -- bd_arbiter under a near tie, with a server of round trip S.
//
// The arbiter is built the way gen.py builds it for the routed GLS
// (GLS_MODEL=fid): each LUT6_2 of cells/rtl/bd_arb.v becomes TWO SLICE_LUTX
// bels (one per output, both reading the same pins, as nextpnr packs a
// fractured LUT: gcd_hw_routed.json has ustate$LUT6/ustate$LUT5 and
// ugrant$LUT6/ugrant$LUT5 in one site), every sink pin gets its own transport
// ICBUF (-DGLS_TRANSPORT_IC), and a bel whose output is routed back into one
// of its OWN pins is a state node: META6=1, TLOOP6 = feedback wire + that
// pin's arc, FB6 = that pin (gen.py fid_loop / fid_fb).  That is ustate$LUT6
// (q, feedback on A3) and ua1/ua2 (bd_c2, own output on A3).  ustate$LUT5 (R0)
// reads q through a wire from another bel, so it is not a state node, exactly
// as gen.py decides.  INITs are bd_arb.v's / bd_ce.v's, pins in logical order
// (I0 = A1 ...): gen.py pre-applies nextpnr's pin permutation, so a permuted
// route differs from this only by which arc each pin has, and every O6 arc
// here is T (every O5 arc T + T5D).
//
// Server: A0 <= #S R0 (transport), i.e. S = R0 output edge to A0 driver edge;
// A0 then reaches each pin through its own wire (~TW).  Clients are four-phase:
// raise r, wait ack, CD later drop r, wait ack low.
//
// One trial: put q at QP with a lone transaction of the client that sets it,
// idle, then the client that must FLIP q raises r at t0 and the other at t0+W.
// Per trial:
//   grants exclusive    no g1&g2 overlap wider than TOL (the O5/O6 decode skew)
//   one ack per cycle   at most one A1/A2 rise between successive A0 rises,
//                       and acks == server transactions == 2
//   no hang, no x at the end of the trial
// and the resolver events (ustate: META / BREAK / rejected runt; ua1+ua2) in
// that trial.  Each violating trial prints a "V" line; "SUM" at the end.
// +PASS_MAX=n prints "tb_f3_arbtie PASS" iff violations <= n (run_f3.sh).
`timescale 1ps/1ps
// resolver counters exist only in the fid model; under the default model the
// bench still elaborates, sees no resolver event and so cannot PASS
`ifdef GLS_FID
`define RS(f) u_st.u.r6.f
`define RA(f) (u_a1.u.r6.f + u_a2.u.r6.f)
`else
`define RS(f) 0
`define RA(f) 0
`endif
module tb_f3_arbtie;
    parameter integer T = 124, T5D = 28, TFB = 300, TW = 250, S = 600, CD = 200;
    parameter integer WMIN = -50, WMAX = 524, WSTEP = 1;
    parameter integer TOL = -1;                 // <0: |T5D| + 2
    // MODE 0: near tie from idle (above).  MODE 1: hold release -- the holder
    // (client 1 for QP=0, client 2 for QP=1) owns the resource, the other's
    // request is up and waiting, the holder drops its request (so A0 falls,
    // releasing q's hold) and RE-RAISES it at W ps relative to the predicted
    // A0 fall at the server (measured: off=).  legal=1 iff the holder's old
    // ack was already low when it re-raised (a four-phase client may);
    // legal=0 stands for a client that is faster than its own ack, or
    // equivalently A0 routed late to ustate.
    parameter integer MODE = 0;
    localparam integer TL = TFB + T;            // TLOOP of q and of ua1/ua2
    localparam integer TOLV = (TOL >= 0) ? TOL : ((T5D < 0) ? -T5D : T5D) + 2;

    reg r1 = 1'bx, r2 = 1'bx, rst = 1'b1;
    wire q, R0, g1, g2, A1, A2;
    reg A0 = 1'bx;
    initial #1 A0 = 1'b0;
    always @(R0) A0 <= #(S) R0;

    // one wire per sink pin (deliberately unequal, a few tens of ps)
    wire q_st, q_r0, q_g6, q_g5, a0_st, a0_r0, a0_1, a0_2;
    wire r1_st, r2_st, r1_r0, r2_r0, r1_g6, r2_g6, r1_g5, r2_g5, g1a, g2a, A1fb, A2fb, rst_d;
    ICBUF #(.D(TFB))     w00 (.I(q),  .O(q_st));
    ICBUF #(.D(TFB))     w01 (.I(q),  .O(q_r0));
    ICBUF #(.D(TW + 40)) w02 (.I(q),  .O(q_g6));
    ICBUF #(.D(TW + 40)) w03 (.I(q),  .O(q_g5));
    ICBUF #(.D(TW))      w04 (.I(A0), .O(a0_st));
    ICBUF #(.D(TW))      w05 (.I(A0), .O(a0_r0));
    ICBUF #(.D(TW + 20)) w06 (.I(A0), .O(a0_1));
    ICBUF #(.D(TW - 20)) w07 (.I(A0), .O(a0_2));
    ICBUF #(.D(TW))      w08 (.I(r1), .O(r1_st));
    ICBUF #(.D(TW + 15)) w09 (.I(r2), .O(r2_st));
    ICBUF #(.D(TW))      w10 (.I(r1), .O(r1_r0));
    ICBUF #(.D(TW + 15)) w11 (.I(r2), .O(r2_r0));
    ICBUF #(.D(TW + 30)) w12 (.I(r1), .O(r1_g6));
    ICBUF #(.D(TW + 25)) w13 (.I(r2), .O(r2_g6));
    ICBUF #(.D(TW + 30)) w14 (.I(r1), .O(r1_g5));
    ICBUF #(.D(TW + 25)) w15 (.I(r2), .O(r2_g5));
    ICBUF #(.D(TW))      w16 (.I(g1), .O(g1a));
    ICBUF #(.D(TW + 35)) w17 (.I(g2), .O(g2a));
    ICBUF #(.D(TFB))     w18 (.I(A1), .O(A1fb));
    ICBUF #(.D(TFB))     w19 (.I(A2), .O(A2fb));
    ICBUF #(.D(TW))      w20 (.I(rst), .O(rst_d));

    localparam [63:0] ST = 64'hFFF0_FFB2_ACAC_ACAC, GR = 64'h0C0C_0C0C_A0A0_A0A0, C2 = 64'h00E8_00E8_00E8_00E8;
    // ustate: O6 q = rst + C(r1,~r2) held while A0 (state node, fb on A3); O5 R0
    SLICE_LUTX #(.INIT(ST), .TA1O6(T), .TA2O6(T), .TA3O6(T), .TA4O6(T), .TA5O6(T), .TA6O6(T),
                 .META6(1), .TLOOP6(TL), .FB6(6'b000100), .SEED(3)) u_st (
        .A1(r1_st), .A2(r2_st), .A3(q_st), .A4(rst_d), .A5(a0_st), .A6(1'b1), .O6(q), .O5());
    SLICE_LUTX #(.INIT(ST), .TA1O5(T + T5D), .TA2O5(T + T5D), .TA3O5(T + T5D), .TA4O5(T + T5D),
                 .TA5O5(T + T5D), .SEED(5)) u_r0 (
        .A1(r1_r0), .A2(r2_r0), .A3(q_r0), .A4(rst_d), .A5(a0_r0), .A6(1'b1), .O6(), .O5(R0));
    // ugrant: O6 g2 = r2.~q, O5 g1 = r1.q
    SLICE_LUTX #(.INIT(GR), .TA1O6(T), .TA2O6(T), .TA3O6(T), .TA4O6(T), .TA5O6(T), .TA6O6(T), .SEED(7)) u_g2 (
        .A1(r1_g6), .A2(r2_g6), .A3(q_g6), .A4(1'b0), .A5(1'b0), .A6(1'b1), .O6(g2), .O5());
    SLICE_LUTX #(.INIT(GR), .TA1O5(T + T5D), .TA2O5(T + T5D), .TA3O5(T + T5D), .TA4O5(T + T5D),
                 .TA5O5(T + T5D), .SEED(9)) u_g1 (
        .A1(r1_g5), .A2(r2_g5), .A3(q_g5), .A4(1'b0), .A5(1'b0), .A6(1'b1), .O6(), .O5(g1));
    // ua1 / ua2: bd_c2 = C(g, A0), I0 g, I1 A0, I2 own output, I3 rst
    SLICE_LUTX #(.INIT(C2), .TA1O6(T), .TA2O6(T), .TA3O6(T), .TA4O6(T), .TA5O6(T), .TA6O6(T),
                 .META6(1), .TLOOP6(TL), .FB6(6'b000100), .SEED(11)) u_a1 (
        .A1(g1a), .A2(a0_1), .A3(A1fb), .A4(rst_d), .A5(1'b0), .A6(1'b0), .O6(A1), .O5());
    SLICE_LUTX #(.INIT(C2), .TA1O6(T), .TA2O6(T), .TA3O6(T), .TA4O6(T), .TA5O6(T), .TA6O6(T),
                 .META6(1), .TLOOP6(TL), .FB6(6'b000100), .SEED(13)) u_a2 (
        .A1(g2a), .A2(a0_2), .A3(A2fb), .A4(rst_d), .A5(1'b0), .A6(1'b0), .O6(A2), .O5());

    // ---- per-trial monitors ----
    reg live = 0, inov = 0;
    integer nsrv, nack, acyc, dbl, novg, xs;
    time tg, gwid;
    always @(posedge A0) if (live) begin nsrv = nsrv + 1; acyc = 0; end
    always @(posedge A1 or posedge A2) if (live) begin
        nack = nack + 1; acyc = acyc + 1; if (acyc > 1) dbl = dbl + 1;
    end
    always @(g1 or g2) if (live) begin
        if (g1 === 1'b1 && g2 === 1'b1) begin if (!inov) begin tg = $time; inov = 1; end end
        else if (inov) begin
            if ($time - tg > gwid) gwid = $time - tg;
            if ($time - tg > TOLV) novg = novg + 1;
            inov = 0;
        end
    end
    wire anyx = (q !== 1'b0 && q !== 1'b1) || (g1 !== 1'b0 && g1 !== 1'b1) || (g2 !== 1'b0 && g2 !== 1'b1)
             || (A1 !== 1'b0 && A1 !== 1'b1) || (A2 !== 1'b0 && A2 !== 1'b1) || (R0 !== 1'b0 && R0 !== 1'b1);
    always @(posedge anyx) if (live) xs = xs + 1;

    // ---- four-phase clients (disable-able, so a hung trial can be cleared) ----
    reg go1 = 0, go2 = 0;
    integer done1 = 0, done2 = 0;
    // MODE 1: the holder's re-raise
    reg goh = 0, legal = 1'b1;
    integer hq = 0, nv_legal = 0, n_legal = 0;
    time trise = 0, ta0f = 0;
    always @(posedge goh) begin : hr
        #(TW + T + T5D + S + W);
        trise = $time;
        if (hq == 0) begin
            legal = (A1 === 1'b0); r1 = 1'b1; wait (A1 === 1'b0); wait (A1 === 1'b1);
            #(CD) r1 = 1'b0; wait (A1 === 1'b0); done1 = done1 + 1;
        end else begin
            legal = (A2 === 1'b0); r2 = 1'b1; wait (A2 === 1'b0); wait (A2 === 1'b1);
            #(CD) r2 = 1'b0; wait (A2 === 1'b0); done2 = done2 + 1;
        end
        goh = 0;
    end
    always @(negedge A0) if (live && ta0f == 0) ta0f = $time;
    always @(posedge go1) begin : c1
        r1 = 1'b1; wait (A1 === 1'b1); #(CD) r1 = 1'b0; wait (A1 === 1'b0);
        done1 = done1 + 1; go1 = 0;
    end
    always @(posedge go2) begin : c2
        r2 = 1'b1; wait (A2 === 1'b1); #(CD) r2 = 1'b0; wait (A2 === 1'b0);
        done2 = done2 + 1; go2 = 0;
    end

    integer W, QP, d1, d2, hang, k, pass_max, verbose;
    integer m0, b0, j0, a0m, ntr = 0, nviol = 0, nv_meta = 0, nv_brk = 0, nv_rej = 0, nv_none = 0;
    integer n_dbl = 0, n_ovg = 0, n_cnt = 0, n_hang = 0, n_xend = 0, n_tmeta = 0, n_prep = 0;
    integer dm, db, dj, da, v;
    time tst, wmax_g = 0;
    task lone(input integer c);
        begin
            if (c == 1) begin d1 = done1; go1 = 1; wait (done1 == d1 + 1); end
            else begin d2 = done2; go2 = 1; wait (done2 == d2 + 1); end
            #6000;
        end
    endtask
    task reset_all;
        begin
            disable c1; disable c2; disable hr; go1 = 0; go2 = 0; goh = 0; r1 = 1'b0; r2 = 1'b0;
            #2000 rst = 1'b1; #3000 rst = 1'b0; #6000;
        end
    endtask
    initial begin
        pass_max = -1; verbose = 0;
        if ($value$plusargs("PASS_MAX=%d", pass_max)) ;
        if ($value$plusargs("TB_VERBOSE=%d", verbose)) ;
        if ($test$plusargs("MON"))
            $monitor("%0t r1=%b r2=%b q=%b g1=%b g2=%b R0=%b A0=%b A1=%b A2=%b", $time, r1, r2, q, g1, g2, R0, A0, A1, A2);
        #1 r1 = 1'b0; r2 = 1'b0;
        #3999 rst = 1'b0;
        #6000;
        for (QP = 0; QP < 2; QP = QP + 1)
            for (W = WMIN; W <= WMAX; W = W + WSTEP) begin
              if (MODE == 1) begin
                if (QP == 0) begin r1 = 1'b1; wait (A1 === 1'b1); go2 = 1; end
                else begin r2 = 1'b1; wait (A2 === 1'b1); go1 = 1; end
                #2000;
                nsrv = 0; nack = 0; acyc = 1; dbl = 0; novg = 0; xs = 0; inov = 0; gwid = 0;
                m0 = `RS(n_meta); b0 = `RS(n_break); j0 = `RS(n_rej);
                a0m = `RA(n_meta) + `RA(n_rej);
                d1 = done1; d2 = done2; ta0f = 0;
                live = 1;
                if (QP == 0) r1 = 1'b0; else r2 = 1'b0;
                hq = QP; goh = 1;
              end else begin
                if (QP == 0) lone(2); else lone(1);          // q -> QP
                if (q !== QP) begin n_prep = n_prep + 1; reset_all; if (QP == 0) lone(2); else lone(1); end
                nsrv = 0; nack = 0; acyc = 0; dbl = 0; novg = 0; xs = 0; inov = 0; gwid = 0;
                m0 = `RS(n_meta); b0 = `RS(n_break); j0 = `RS(n_rej);
                a0m = `RA(n_meta) + `RA(n_rej);
                d1 = done1; d2 = done2;
                live = 1;
                // QP=0: client 1 must set q; QP=1: client 2 must reset it
                if (W >= 0) begin
                    if (QP == 0) begin go1 = 1; #(W) go2 = 1; end else begin go2 = 1; #(W) go1 = 1; end
                end else begin
                    if (QP == 0) begin go2 = 1; #(-W) go1 = 1; end else begin go1 = 1; #(-W) go2 = 1; end
                end
              end
                tst = $time; hang = 0;
                while (!(done1 == d1 + 1 && done2 == d2 + 1) && !hang) begin
                    #100; if ($time - tst > 200000) hang = 1;
                end
                #6000;
                live = 0;
                dm = `RS(n_meta) - m0; db = `RS(n_break) - b0; dj = `RS(n_rej) - j0;
                da = `RA(n_meta) + `RA(n_rej) - a0m;
                ntr = ntr + 1;
                if (dm) n_tmeta = n_tmeta + 1;
                if (gwid > wmax_g) wmax_g = gwid;
                v = 0;
                if (dbl) begin n_dbl = n_dbl + 1; v = 1; end
                if (novg) begin n_ovg = n_ovg + 1; v = 1; end
                if (!hang && (nack != 2 || nsrv != 2)) begin n_cnt = n_cnt + 1; v = 1; end
                if (hang) begin n_hang = n_hang + 1; v = 1; end
                if (anyx) begin n_xend = n_xend + 1; v = 1; end
                if (MODE == 1 && legal) n_legal = n_legal + 1;
                if (v) begin
                    nviol = nviol + 1;
                    if (MODE == 1 && legal) nv_legal = nv_legal + 1;
                    if (dm) nv_meta = nv_meta + 1;
                    if (db) nv_brk = nv_brk + 1;
                    if (dj && !dm) nv_rej = nv_rej + 1;
                    if (!dm && !db && !dj) nv_none = nv_none + 1;
                end
                if (v || verbose)
                    $display("%s QP=%0d W=%0d meta=%0d break=%0d rej=%0d ua_ev=%0d srv=%0d ack=%0d dbl=%0d ovg=%0d gw=%0t x=%0d xend=%b hang=%0d trp=%0d delta=%0d legal=%b off=%0d",
                             v ? "V" : "T", QP, W, dm, db, dj, da, nsrv, nack, dbl, novg, gwid, xs, anyx, hang,
                             `RS(trp), `RS(delta), legal, (MODE == 1) ? $signed(trise - ta0f) : 0);
                if (hang || anyx) reset_all;
            end
        $display("SUM TLOOP=%0d S=%0d T=%0d trials=%0d meta_trials=%0d viol=%0d (dblack=%0d ovg=%0d count=%0d hang=%0d xend=%0d) viol_meta=%0d viol_break=%0d viol_rejonly=%0d viol_noevent=%0d widest_overlap=%0t tol=%0d prepfail=%0d mode=%0d legal_trials=%0d viol_legal=%0d",
                 TL, S, T, ntr, n_tmeta, nviol, n_dbl, n_ovg, n_cnt, n_hang, n_xend, nv_meta, nv_brk, nv_rej, nv_none, wmax_g, TOLV, n_prep, MODE, n_legal, nv_legal);
        if (pass_max >= 0) begin
            if (nviol <= pass_max && n_tmeta > 0) $display("tb_f3_arbtie PASS");
            else $display("tb_f3_arbtie FAIL (violations %0d > %0d, or no resolver event: %0d)", nviol, pass_max, n_tmeta);
        end
        $finish;
    end
endmodule
`undef RS
`undef RA
