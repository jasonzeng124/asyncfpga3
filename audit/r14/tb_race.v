// audit r14: own race bench for FID_RESOLVE (fid_core.vh at research 6524fa3 == wt-r13).
// K independent copies of a C(r1,~r2) state LUT (INIT derived here: 0xB2 on
// A1=r1,A2=r2,A3=q_fb; A4=rst forces 0) with a transport feedback wire FB.
// r1 rises, r2 rises DT later; r1 wins iff q settles to 1.
`timescale 1ps/1ps
module fbwire(input wire i, output reg o);
  parameter integer D = 300;
  initial o = 1'b0;
  always @(i) o <= #(D) i;
endmodule
module tb_race;
  parameter integer K = 400, FB = 300, TP = 124;
  integer DT, NTR, k, t, w1, w2, wx, edges, trace;
  reg r1 = 0, r2 = 0, rst = 1;
  wire [K-1:0] q, qf;
  genvar g;
  generate for (g = 0; g < K; g = g + 1) begin : c
    FID_LUT6 #(.INIT(64'h0000_0000_0000_00B2), .T1_6(TP), .T2_6(TP), .T3_6(TP),
               .T4_6(TP), .TLOOP6(FB + TP), .SEED(g + 1)) u (
      .A1(r1), .A2(r2), .A3(qf[g]), .A4(rst), .A5(1'b0), .A6(1'b0),
      .EN6(1'b1), .EN5(1'b0), .O5(), .O6(q[g]));
    fbwire #(.D(FB)) w (.i(q[g]), .o(qf[g]));
  end endgenerate
  always @(q[0]) if (trace) $display("  q0 %b @%0t", q[0], $time);
  initial begin
    DT = 200; NTR = 1; trace = 0;
    if ($value$plusargs("DT=%d", DT)) ;
    if ($value$plusargs("NTR=%d", NTR)) ;
    if ($value$plusargs("TRACE=%d", trace)) ;
    w1 = 0; w2 = 0; wx = 0;
    for (t = 0; t < NTR; t = t + 1) begin
      rst = 1; #5000 rst = 0; #5000;
      r1 = 1; #(DT) r2 = 1;
      #20000;
      for (k = 0; k < K; k = k + 1)
        if (q[k] === 1'b1) w1 = w1 + 1; else if (q[k] === 1'b0) w2 = w2 + 1; else wx = wx + 1;
      r1 = 0; r2 = 0;
    end
    $display("RACE TLOOP=%0d DT=%0d r1won=%0d r2won=%0d x=%0d frac_r1=%0.3f",
             FB + TP, DT, w1, w2, wx, (1.0 * w1) / (w1 + w2 + wx));
    $finish;
  end
endmodule
