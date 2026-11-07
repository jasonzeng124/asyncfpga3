`timescale 1ps/1ps
// bd_arbiter (cells/rtl/bd_arb.v:236-261) as the fid GLS builds it (prims.v GLS_FID SLICE_LUTX,
// transport ICBUFs): ustate O6 = q is a state node (META6=1, TLOOP6 = feedback wire + A3 arc),
// ustate O5 = R0 a plain LUT (nextpnr splits the LUT6_2 into two SLICE_LUTX), ugrant O5/O6
// plain, ua1/ua2 = bd_c2 state nodes. The server is A0 <= #SMIN R0 (transport).
// Delays (chosen so that GLSResolveGen.arb_double_ack's single-delay hypotheses hold):
//   every arc T = 50, feedback pins T3 = 100, every wire TW = 100, except r1/r2 -> ugrant
//   TR = 150 (so ugrant sees r and q both 150 ps after ustate's mux does).
// Clients: r1 rises at TB, r2 at TB + W (a near tie), both stay high.
module tb_arb;
  parameter integer TW = 100, T3 = 100, T = 50, TR = 150, W = 150, SMIN = 300;
  reg r1 = 1'bx, r2 = 1'bx, rst = 1'b1;   // driven at 1 ps: an ICBUF copies only events
  wire q, R0, g1, g2, A1, A2;
  reg A0 = 1'bx;
  initial #1 A0 = 1'b0;
  always @(R0) if (R0 === 1'b0 || R0 === 1'b1) A0 <= #(SMIN) R0;
  wire q_st, q_gr, q_r0, a0_st, a0_r0, a0_1, a0_2, r1g, r2g, g1a, g2a, A1fb, A2fb;
  ICBUF #(.D(TW)) w1 (.I(q), .O(q_st));
  ICBUF #(.D(TW)) w2 (.I(q), .O(q_gr));
  ICBUF #(.D(TW)) w3 (.I(q), .O(q_r0));
  ICBUF #(.D(TW)) w4 (.I(A0), .O(a0_st));
  ICBUF #(.D(TW)) w5 (.I(A0), .O(a0_r0));
  ICBUF #(.D(TW)) w6 (.I(A0), .O(a0_1));
  ICBUF #(.D(TW)) w7 (.I(A0), .O(a0_2));
  ICBUF #(.D(TR)) w8 (.I(r1), .O(r1g));
  ICBUF #(.D(TR)) w9 (.I(r2), .O(r2g));
  ICBUF #(.D(TW)) w10 (.I(g1), .O(g1a));
  ICBUF #(.D(TW)) w11 (.I(g2), .O(g2a));
  ICBUF #(.D(TW)) w12 (.I(A1), .O(A1fb));
  ICBUF #(.D(TW)) w13 (.I(A2), .O(A2fb));
  // ustate, O6 = q: I0 r1, I1 r2, I2 q, I3 rst, I4 A0, I5 1
  SLICE_LUTX #(.INIT(64'hFFF0_FFB2_ACAC_ACAC), .TA1O6(T), .TA2O6(T), .TA3O6(T3), .TA4O6(T),
               .TA5O6(T), .TA6O6(T), .META6(1), .TLOOP6(TW + T3), .SEED(11)) u_st
    (.A1(r1), .A2(r2), .A3(q_st), .A4(rst), .A5(a0_st), .A6(1'b1), .O6(q), .O5());
  // ustate, O5 = R0 (its own SLICE_LUTX, no self-loop)
  SLICE_LUTX #(.INIT(64'hFFF0_FFB2_ACAC_ACAC), .TA1O5(T), .TA2O5(T), .TA3O5(T), .TA4O5(T),
               .TA5O5(T), .SEED(12)) u_r0
    (.A1(r1), .A2(r2), .A3(q_r0), .A4(rst), .A5(a0_r0), .A6(1'b1), .O6(), .O5(R0));
  // ugrant: O5 = g1 = r1.q, O6 = g2 = r2.~q
  SLICE_LUTX #(.INIT(64'h0C0C_0C0C_A0A0_A0A0), .TA1O6(T), .TA2O6(T), .TA3O6(T),
               .TA1O5(T), .TA2O5(T), .TA3O5(T), .SEED(13)) u_gr
    (.A1(r1g), .A2(r2g), .A3(q_gr), .A4(1'b0), .A5(1'b0), .A6(1'b1), .O6(g2), .O5(g1));
  // ua1 / ua2 = bd_c2: I0 g, I1 A0, I2 own output, I3 rst
  SLICE_LUTX #(.INIT(64'h00E8_00E8_00E8_00E8), .TA1O6(T), .TA2O6(T), .TA3O6(T3), .TA4O6(T),
               .META6(1), .TLOOP6(TW + T3), .SEED(14)) u_a1
    (.A1(g1a), .A2(a0_1), .A3(A1fb), .A4(rst), .A5(1'b0), .A6(1'b0), .O6(A1), .O5());
  SLICE_LUTX #(.INIT(64'h00E8_00E8_00E8_00E8), .TA1O6(T), .TA2O6(T), .TA3O6(T3), .TA4O6(T),
               .META6(1), .TLOOP6(TW + T3), .SEED(15)) u_a2
    (.A1(g2a), .A2(a0_2), .A3(A2fb), .A4(rst), .A5(1'b0), .A6(1'b0), .O6(A2), .O5());
  initial begin
    $monitor("%0t q=%b g1=%b g2=%b R0=%b A0=%b A1=%b A2=%b", $time, q, g1, g2, R0, A0, A1, A2);
    // rst drives q to 1 (bd_arb.v:233); one client-2 transaction leaves the arbiter idle at q = 0
    #1 r1 = 1'b0; r2 = 1'b0;
    #1999 rst = 1'b0;
    #3000 r2 = 1'b1;
    @(posedge A2) #500 r2 = 1'b0;
    @(negedge A2) #5000;
    $display("TIE tb=%0t w=%0d smin=%0d", $time, W, SMIN);
    r1 = 1'b1; #(W) r2 = 1'b1;
    #20000 $finish;
  end
endmodule
