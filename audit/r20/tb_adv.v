// audit r20: adversarial stimuli for the 055edd74 FID_RESOLVE (same C-element as tb_c2r.v:
// INIT 0x00E8 = maj(A1,A2,A3) with A4 = rst, A3 = q via a 100 ps wire, arc 100, TLOOP 200).
// b waveform: NP pulses of H ps high separated by L ps low, starting at 7000; b then stays
// at ENDV.  +GAP2/+W2 adds a later pulse. Prints final q of K seeded copies + edge count.
`timescale 1ps/1ps
module fbwire(input wire i, output reg o);
  parameter integer D = 100;
  initial o = 1'b0;
  always @(i) o <= #(D) i;
endmodule
module tb_adv;
  parameter integer K = 40, FB = 100, T3 = 100, TA = 50;
  integer NP, H, L, ENDV, n, k, W2, GAP2, BX, BXG;
  reg a = 0, b = 0, rst = 1;
  wire [K-1:0] q, qf;
  integer ne [0:K-1];
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
    initial ne[g] = 0;
    always @(q[g]) if ($time > 6000) ne[g] = ne[g] + 1;
  end endgenerate
  integer n1, n0, nx, emax;
  initial begin
    NP = 1; H = 20; L = 1; ENDV = 0; W2 = 0; GAP2 = 0;
    if ($value$plusargs("NP=%d", NP)) ; if ($value$plusargs("H=%d", H)) ;
    if ($value$plusargs("L=%d", L)) ;   if ($value$plusargs("ENDV=%d", ENDV)) ;
    BX = 0; BXG = 1; if ($value$plusargs("BX=%d", BX)) ; if ($value$plusargs("BXG=%d", BXG)) ;
    if ($value$plusargs("W2=%d", W2)) ; if ($value$plusargs("GAP2=%d", GAP2)) ;
    #5000 rst = 0; a = 1;
    #2000;
    for (n = 0; n < NP; n = n + 1) begin b = 1; #(H) b = 0; if (n < NP - 1) #(L); end
    if (ENDV) b = 1;
    if (BX > 0) begin #(BXG) b = 1'bx; #(BX) b = 0; end
    if (W2 > 0) begin #(GAP2) b = 1; #(W2) b = 0; end
    #30000;
    n1 = 0; n0 = 0; nx = 0; emax = 0;
    for (k = 0; k < K; k = k + 1) begin
      if (q[k] === 1'b1) n1 = n1 + 1; else if (q[k] === 1'b0) n0 = n0 + 1; else nx = nx + 1;
      if (ne[k] > emax) emax = ne[k];
    end
    $display("RES NP=%0d H=%0d L=%0d ENDV=%0d GAP2=%0d W2=%0d: q=1 %0d q=0 %0d x %0d  max q edges %0d",
             NP, H, L, ENDV, GAP2, W2, n1, n0, nx, emax);
    $display("QV %b", q);
    $finish;
  end
endmodule
