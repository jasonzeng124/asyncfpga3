// audit r16: XOR of one edge through two pins at 45 / 124 ps (formal xor_o6) vs equal arcs.
`timescale 1ps/1ps
module tb_xor;
  reg x = 0; wire om, oe;
  FID_LUT6 #(.INIT(64'h6666666666666666), .T1_6(45), .T2_6(124)) um (.A1(x), .A2(x), .A3(1'b0),
    .A4(1'b0), .A5(1'b0), .A6(1'b0), .EN6(1'b0), .EN5(1'b0), .O5(), .O6(om));
  FID_LUT6 #(.INIT(64'h6666666666666666), .T1_6(124), .T2_6(124)) ue (.A1(x), .A2(x), .A3(1'b0),
    .A4(1'b0), .A5(1'b0), .A6(1'b0), .EN6(1'b0), .EN5(1'b0), .O5(), .O6(oe));
  always @(om) $display("mixed %b @%0t", om, $time);
  always @(oe) $display("equal %b @%0t", oe, $time);
  initial begin #1000 x = 1; #2000 $finish; end
endmodule
