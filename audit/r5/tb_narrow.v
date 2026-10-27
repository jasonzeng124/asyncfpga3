`timescale 1ps/1ps
module tb;
  reg a = 0;
  wire o5, o6;
  SLICE_LUTX #(.INIT(64'h2), .TA1O6(124)) u (.A1(a), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(o5), .O6(o6));
  integer n = 0, w;
  always @(o6) if ($time > 500) n = n + 1;
  initial begin
    #1000;
    for (w = 1; w <= 4; w = w + 1) begin
      n = 0; a = 1; #(w) a = 0; #1000;
      $display("pulse %0d ps -> %0d output edges", w, n);
    end
    // two pulses 1 ps wide, 1 ps apart
    n = 0; a = 1; #1 a = 0; #1 a = 1; #1 a = 0; #1000;
    $display("1ps/1ps/1ps train -> %0d output edges (transport: 4)", n);
    $finish;
  end
endmodule
