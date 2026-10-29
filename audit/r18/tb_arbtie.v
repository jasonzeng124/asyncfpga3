// audit r18: own bench. bd_arbiter (wt-r17 cells/rtl/bd_arb.v, md5 27dfc230) built the way
// the fid GLS builds it: every LUT6_2 split into two SLICE_LUTX (gls/prims.v GLS_FID, md5
// 3e7423cb; fid_core.vh md5 2422ccea), state nodes = LUTs whose output feeds their own pin
// (ustate O6 = q, ua1, ua2) get META6=1, TLOOP6 = feedback wire + feedback pin arc (gen.py
// fid_loop rule). All wires are transport (GLS_TRANSPORT_IC ICBUF).
// Trials: put q at QP by a lone transaction, idle, then near tie: the client that must
// FLIP q rises at t0, the other at t0+W. Server = transport delay S on R0 (A0 <= #S R0),
// clients four-phase (drop r on ack, wait ack low). Per trial: server transactions (A0
// rises), client acks (A1/A2 rises), A1&A2 overlap, g1&g2 overlap, X after reset, resolver
// events on q. Violation = acks > server transactions.
`timescale 1ps/1ps
module tb_arbtie;
  parameter integer T = 124, TFB = 300, TW = 250, S = 600, WMIN = -200, WMAX = 600, WSTEP = 4;
  reg r1 = 1'bx, r2 = 1'bx, rst = 1'b1;
  wire q, R0, g1, g2, A1, A2;
  reg A0 = 1'bx;
  initial #1 A0 = 1'b0;
  always @(R0) A0 <= #(S) R0;
  wire q_st, q_gr, q_r0, a0_st, a0_r0, a0_1, a0_2, r1s, r2s, r1r, r2r, r1g, r2g, g1a, g2a, A1fb, A2fb;
  ICBUF #(.D(TFB)) w1 (.I(q), .O(q_st));        // feedback
  ICBUF #(.D(TW+40)) w2 (.I(q), .O(q_gr));
  ICBUF #(.D(TW-30)) w3 (.I(q), .O(q_r0));
  ICBUF #(.D(TW)) w4 (.I(A0), .O(a0_st));
  ICBUF #(.D(TW+10)) w5 (.I(A0), .O(a0_r0));
  ICBUF #(.D(TW+20)) w6 (.I(A0), .O(a0_1));
  ICBUF #(.D(TW-20)) w7 (.I(A0), .O(a0_2));
  ICBUF #(.D(TW)) w8 (.I(r1), .O(r1s));
  ICBUF #(.D(TW+15)) w9 (.I(r2), .O(r2s));
  ICBUF #(.D(TW-10)) w10 (.I(r1), .O(r1r));
  ICBUF #(.D(TW+5)) w11 (.I(r2), .O(r2r));
  ICBUF #(.D(TW+30)) w12 (.I(r1), .O(r1g));
  ICBUF #(.D(TW+25)) w13 (.I(r2), .O(r2g));
  ICBUF #(.D(TW)) w14 (.I(g1), .O(g1a));
  ICBUF #(.D(TW+35)) w15 (.I(g2), .O(g2a));
  ICBUF #(.D(TFB)) w16 (.I(A1), .O(A1fb));
  ICBUF #(.D(TFB)) w17 (.I(A2), .O(A2fb));
  // ustate O6: q = rst + C(r1,~r2) held while A0.  pins A1..A6 = I0..I5
  SLICE_LUTX #(.INIT(64'hFFF0_FFB2_ACAC_ACAC), .TA1O6(T), .TA2O6(T), .TA3O6(T), .TA4O6(T),
     .TA5O6(T), .TA6O6(T), .META6(1), .TLOOP6(TFB + T), .SEED(3)) u_st
    (.A1(r1s), .A2(r2s), .A3(q_st), .A4(rst), .A5(a0_st), .A6(1'b1), .O6(q), .O5());
  // ustate O5: R0 = r1.q + r2.~q (own bel, no self loop); O5 arcs a bit slower than O6
  SLICE_LUTX #(.INIT(64'hFFF0_FFB2_ACAC_ACAC), .TA1O5(T+20), .TA2O5(T+20), .TA3O5(T+20),
     .TA4O5(T+20), .TA5O5(T+20), .SEED(5)) u_r0
    (.A1(r1r), .A2(r2r), .A3(q_r0), .A4(rst), .A5(a0_r0), .A6(1'b1), .O6(), .O5(R0));
  // ugrant: O5 = g1 = r1.q, O6 = g2 = r2.~q
  SLICE_LUTX #(.INIT(64'h0C0C_0C0C_A0A0_A0A0), .TA1O6(T), .TA2O6(T), .TA3O6(T),
     .SEED(7)) u_g2 (.A1(r1g), .A2(r2g), .A3(q_gr), .A4(1'b0), .A5(1'b0), .A6(1'b1), .O6(g2), .O5());
  SLICE_LUTX #(.INIT(64'h0C0C_0C0C_A0A0_A0A0), .TA1O5(T+20), .TA2O5(T+20), .TA3O5(T+20),
     .SEED(9)) u_g1 (.A1(r1g), .A2(r2g), .A3(q_gr), .A4(1'b0), .A5(1'b0), .A6(1'b1), .O6(), .O5(g1));
  // ua1/ua2 = bd_c2 (INIT 00E8...): I0 g, I1 A0, I2 own q, I3 rst
  SLICE_LUTX #(.INIT(64'h00E8_00E8_00E8_00E8), .TA1O6(T), .TA2O6(T), .TA3O6(T), .TA4O6(T),
     .META6(1), .TLOOP6(TFB + T), .SEED(11)) u_a1
    (.A1(g1a), .A2(a0_1), .A3(A1fb), .A4(rst), .A5(1'b0), .A6(1'b0), .O6(A1), .O5());
  SLICE_LUTX #(.INIT(64'h00E8_00E8_00E8_00E8), .TA1O6(T), .TA2O6(T), .TA3O6(T), .TA4O6(T),
     .META6(1), .TLOOP6(TFB + T), .SEED(13)) u_a2
    (.A1(g2a), .A2(a0_2), .A3(A2fb), .A4(rst), .A5(1'b0), .A6(1'b0), .O6(A2), .O5());

  // ---- per-trial counters ----
  integer nsrv = 0, nack1 = 0, nack2 = 0, ovA = 0, ovG = 0, xs = 0, live = 0;
  time tg = 0, gw = 0, tq = 0;
  always @(posedge A0) if (live) nsrv = nsrv + 1;
  always @(posedge A1) if (live) nack1 = nack1 + 1;
  always @(posedge A2) if (live) nack2 = nack2 + 1;
  always @(A1 or A2) if (live && A1 === 1'b1 && A2 === 1'b1) ovA = ovA + 1;
  always @(g1 or g2) if (live) begin
    if (g1 === 1'b1 && g2 === 1'b1) begin ovG = ovG + 1; tg = $time; end
    else if (tg != 0) begin if ($time - tg > gw) gw = $time - tg; tg = 0; end
  end
  always @(q or g1 or g2 or A1 or A2 or R0 or A0)
    if (live && ((q !== 1'b0 && q !== 1'b1) || (g1 !== 1'b0 && g1 !== 1'b1) || (g2 !== 1'b0 && g2 !== 1'b1)
        || (A1 !== 1'b0 && A1 !== 1'b1) || (A2 !== 1'b0 && A2 !== 1'b1) || (R0 !== 1'b0 && R0 !== 1'b1))) xs = xs + 1;
  integer nm0, nc0, trp_l, dl_l;
  always @(u_st.u.r6.n_meta) begin trp_l = u_st.u.r6.trp; dl_l = u_st.u.r6.delta; end

  // four-phase clients
  reg go1 = 0, go2 = 0; integer done1 = 0, done2 = 0;
  always @(posedge go1) begin r1 = 1'b1; wait (A1 === 1'b1); #200 r1 = 1'b0; wait (A1 === 1'b0); done1 = done1 + 1; go1 = 0; end
  always @(posedge go2) begin r2 = 1'b1; wait (A2 === 1'b1); #200 r2 = 1'b0; wait (A2 === 1'b0); done2 = done2 + 1; go2 = 0; end

  integer W, QP, d1, d2, hang;
  time tst;
  task lone(input integer k);
    begin
      if (k == 1) begin d1 = done1; go1 = 1; wait (done1 == d1 + 1); end
      else begin d2 = done2; go2 = 1; wait (done2 == d2 + 1); end
      #8000;
    end
  endtask
  initial begin
    if ($test$plusargs("MON")) $monitor("%0t r1=%b r2=%b q=%b g1=%b g2=%b R0=%b A0=%b A1=%b A2=%b", $time, r1, r2, q, g1, g2, R0, A0, A1, A2);
    #1 r1 = 1'b0; r2 = 1'b0;
    #3999 rst = 1'b0;
    #6000;
    for (QP = 0; QP < 2; QP = QP + 1)
      for (W = WMIN; W <= WMAX; W = W + WSTEP) begin
        // q -> QP: q=1 is set by client 1 alone, q=0 by client 2 alone
        if (QP == 0) lone(2); else lone(1);
        if (q !== QP) $display("PREPFAIL QP=%0d q=%b", QP, q);
        nsrv = 0; nack1 = 0; nack2 = 0; ovA = 0; ovG = 0; gw = 0; tg = 0; xs = 0; live = 1;
        nm0 = u_st.u.r6.n_meta; nc0 = u_st.u.r6.n_commit; trp_l = -1; dl_l = 0;
        d1 = done1; d2 = done2;
        // flipping client first: QP=0 -> client 1 must set q; QP=1 -> client 2 must reset it
        if (W >= 0) begin
          if (QP == 0) begin go1 = 1; #(W) go2 = 1; end else begin go2 = 1; #(W) go1 = 1; end
        end else begin
          if (QP == 0) begin go2 = 1; #(-W) go1 = 1; end else begin go1 = 1; #(-W) go2 = 1; end
        end
        tst = $time; hang = 0;
        while (!(done1 == d1 + 1 && done2 == d2 + 1) && !hang) begin #100; if ($time - tst > 400000) hang = 1; end
        #8000; live = 0;
        $display("T QP=%0d W=%0d meta=%0d commit=%0d trp=%0d delta=%0d srv=%0d ack1=%0d ack2=%0d ovA=%0d ovG=%0d gw=%0t x=%0d hang=%0d",
                 QP, W, u_st.u.r6.n_meta - nm0, u_st.u.r6.n_commit - nc0, trp_l, dl_l,
                 nsrv, nack1, nack2, ovA, ovG, gw, xs, hang);
        if (hang) begin $display("HANG"); $finish; end
      end
    $finish;
  end
endmodule
