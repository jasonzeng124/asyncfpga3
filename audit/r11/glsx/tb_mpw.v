`timescale 1ps/1ps
// Auditor tb (r11): SLICE_FFX clock min-pulse-width and SR-in-aperture.
// One flop per experiment so state never leaks between them.  TSU/THD = SR's
// SDF window (100/100) so the aperture is known; TCKQ 340 (as in BQ#3's SDF).
module tb;
  // ---- MPW: high pulses of width W on CK, D=1 settled, Q starts 0
  reg [7:0] ck; reg d1 = 1, zero = 0, one = 1;
  wire [7:0] q;
  genvar i;
  generate for (i = 0; i < 8; i = i + 1) begin : F
    SLICE_FFX #(.INIT(1'b0), .TCKQ(340), .TSU(100), .THD(100), .SEED(i+1)) f
      (.CK(ck[i]), .D(d1), .CE(one), .SR(zero), .Q(q[i]));
  end endgenerate
  integer w [0:7];
  integer k;
  // ---- low runt: CK high (Q=0 captured with D=0), D->1, CK low gap g, rise
  reg [3:0] lck; reg [3:0] ld; wire [3:0] lq;
  generate for (i = 0; i < 4; i = i + 1) begin : L
    SLICE_FFX #(.INIT(1'b0), .TCKQ(340), .TSU(100), .THD(100), .SEED(i+11)) f
      (.CK(lck[i]), .D(ld[i]), .CE(one), .SR(zero), .Q(lq[i]));
  end endgenerate
  integer g [0:3];
  // ---- SR in aperture: Q=1 first (D=1), then D stays 1, SR rises at offset o
  // relative to CK rise (negative = before).  Old/new next state differ (1 vs 0).
  reg [5:0] sck, ssr; wire [5:0] sq;
  generate for (i = 0; i < 6; i = i + 1) begin : S
    SLICE_FFX #(.INIT(1'b1), .SRVAL(1'b0), .TCKQ(340), .TSU(100), .THD(100), .SEED(i+21)) f
      (.CK(sck[i]), .D(one), .CE(one), .SR(ssr[i]), .Q(sq[i]));
  end endgenerate
  integer o [0:5];
  initial begin
    w[0]=400; w[1]=120; w[2]=95; w[3]=70; w[4]=60; w[5]=45; w[6]=20; w[7]=5;
    g[0]=400; g[1]=60; g[2]=30; g[3]=5;
    o[0]=-1000; o[1]=-60; o[2]=-5; o[3]=5; o[4]=60; o[5]=1000;
    ck = 0; lck = 0; ld = 0; sck = 0; ssr = 0;
    #2000;
    for (k = 0; k < 8; k = k + 1) begin
      ck[k] = 1; #(w[k]) ck[k] = 0; #2000;
      $display("MPW high pulse %0d ps: Q=%b (Q0=0, D=1)", w[k], q[k]);
    end
    for (k = 0; k < 4; k = k + 1) begin
      lck[k] = 1; #1000 ld[k] = 1; #1000 lck[k] = 0; #(g[k]) lck[k] = 1; #2000;
      $display("MPW low gap %0d ps before rise, D 0->1 while CK high: Q=%b", g[k], lq[k]);
      lck[k] = 0;
    end
    for (k = 0; k < 6; k = k + 1) begin
      if (o[k] < 0) begin ssr[k] = 1; #(-o[k]) sck[k] = 1; end
      else begin sck[k] = 1; #(o[k]) ssr[k] = 1; end
      #3000 $display("SR rise at %0d ps vs CK (old next=1, new=0): Q=%b", o[k], sq[k]);
      sck[k] = 0; #1000;
    end
    $finish;
  end
endmodule
