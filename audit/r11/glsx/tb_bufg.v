`timescale 1ps/1ps
// Auditor tb (r11): BUFGCTRL I0->O, 50 ps pulse through a 200 ps arc.
module tb;
  reg i0 = 0; wire o;
  BUFGCTRL #(.TI0O(200)) b (.I0(i0), .I1(1'b0), .S0(1'b1), .S1(1'b0), .CE0(1'b1), .CE1(1'b0), .IGNORE0(1'b0), .IGNORE1(1'b1), .O(o));
  always @(o) $display("O=%b at %0t", o, $time);
  initial begin #1000 i0 = 1; #50 i0 = 0; #1000 i0 = 1; #1000 i0 = 0; #1000 $finish; end
endmodule
