// audit r20 (copy of r16 bench; +define FIDNEW passes FB6 = A3 for the 055edd74 resolver)
// audit r16: own bench for FID_RESOLVE trace semantics (fid_core.vh, wt-r15 21cae6b,
// md5 2422ccea... = the 6524fa3 md5 the formal note cites).
// K independent copies of a C-element state LUT: A1=a, A2=b, A3=q feedback, A4=rst.
// INIT 0x00E8 = maj(a,b,q) when rst=0, 0 when rst=1 (derived here by hand).
// Feedback: transport wire FB, pin arc T3; TLOOP6 = FB + T3. Other arcs TA.
// Stimulus: a=1, b pulse W at time TB (mux arrival TB+TA); optional follow pulse
// W2 starting GAP after the runt's end.  Every q edge of every copy is logged.
`timescale 1ps/1ps
module fbwire(input wire i, output reg o);
  parameter integer D = 100;
  initial o = 1'b0;
  always @(i) o <= #(D) i;
endmodule
module tb_c2r;
  parameter integer K = 40, FB = 100, T3 = 100, TA = 50;
  integer W, W2, GAP, TB;
  reg a = 0, b = 0, rst = 1;
  wire [K-1:0] q, qf;
  genvar g;
  generate for (g = 0; g < K; g = g + 1) begin : c
    FID_LUT6 #(.INIT(64'h0000_0000_0000_00E8), .T1_6(TA), .T2_6(TA), .T3_6(T3),
               .T4_6(TA), .T5_6(TA), .T6_6(TA), .TLOOP6(FB + T3),
`ifdef FIDNEW
               .FB6(`FB6MASK),
`endif
               .SEED(g + 1)) u (
      .A1(a), .A2(b), .A3(qf[g]), .A4(rst), .A5(1'b0), .A6(1'b0),
      .EN6(1'b1), .EN5(1'b0), .O5(), .O6(q[g]));
    fbwire #(.D(FB)) w (.i(q[g]), .o(qf[g]));
    always @(q[g]) $display("E %0d %b %0t", g, q[g], $time);
  end endgenerate
  integer k;
  initial begin
    W = 20; W2 = 0; GAP = 1; TB = 7000;
    if ($value$plusargs("W=%d", W)) ;
    if ($value$plusargs("W2=%d", W2)) ;
    if ($value$plusargs("GAP=%d", GAP)) ;
    $display("CFG W=%0d W2=%0d GAP=%0d TB=%0d TA=%0d TLOOP=%0d", W, W2, GAP, TB, TA, FB+T3);
    #5000 rst = 0; a = 1;
    #(TB - 5000) b = 1;
    #(W) b = 0;
    if (W2 > 0) begin #(GAP) b = 1; #(W2) b = 0; end
    #30000;
    for (k = 0; k < K; k = k + 1) $display("F %0d %b", k, q[k]);
    $finish;
  end
endmodule
