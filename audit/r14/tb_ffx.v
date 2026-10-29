// audit r14: SLICE_FFX fid behaviours claimed FIXED: SR in aperture, CK min pulse width, D transport.
`timescale 1ps/1ps
module tb_ffx;
  parameter integer K = 200;
  integer OFF, PW, k, n1, n0, nx;
  reg ck = 0, d = 0, sr = 0;
  wire [K-1:0] q;
  genvar g;
  generate for (g = 0; g < K; g = g + 1) begin : f
    SLICE_FFX #(.INIT(1'b0), .SRVAL(1'b0), .TCKQ(300), .TSU(100), .THD(100), .SEED(g + 1)) u (
      .CK(ck), .D(d), .CE(1'b1), .SR(sr), .Q(q[g]));
  end endgenerate
  initial begin
    OFF = 0; PW = 0;
    if ($value$plusargs("OFF=%d", OFF)) ;   // SR falls OFF ps before CK (D = 1 held)
    if ($value$plusargs("PW=%d", PW)) ;     // >0: CK high pulse width test instead
    n1 = 0; n0 = 0; nx = 0;
    d = 1; sr = 1; #5000;
    if (PW == 0) begin
      #(1000 - OFF) sr = 0; #(OFF) ck = 1;
    end else begin
      sr = 0; #1000 ck = 1; #(PW) ck = 0;
    end
    #5000;
    for (k = 0; k < K; k = k + 1) if (q[k] === 1'b1) n1 = n1 + 1; else if (q[k] === 1'b0) n0 = n0 + 1; else nx = nx + 1;
    $display("FFX OFF=%0d PW=%0d q=1:%0d q=0:%0d x:%0d", OFF, PW, n1, n0, nx);
    $finish;
  end
endmodule
