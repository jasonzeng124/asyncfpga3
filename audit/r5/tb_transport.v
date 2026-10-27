`timescale 1ps/1ps
module tb;
  reg a = 0;
  wire o5, o6;
  // buffer on A1 (O6 = A1), 124 ps arc; A2..A6 tied 0
  SLICE_LUTX #(.INIT(64'h2), .TA1O6(124)) u (.A1(a), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(o5), .O6(o6));
  integer n = 0;
  always @(o6) if ($time > 500) begin n = n + 1; $display("t=%0t o6=%b", $time, o6); end
  initial begin
    #1000 a = 1; #50 a = 0; #50 a = 1; #50 a = 0;   // pulses 1000-1050, 1100-1150
    #1000 $display("edges=%0d (transport expects 4: 1124 1174 1224 1274)", n);
    $finish;
  end
endmodule
