`timescale 1ps/1ps
// Auditor tb: CARRY4 O0 = S0 ^ CIN.  S0 pulses 1000..1010, CIN rises at 1200.
// Transport (S0 arc 223, CIN arc 222): O0 pulse 1223..1233, then O0 rises at 1422.
// An edge at 1223 that STAYS high would be CIN's edge emerging 23 ps after its cause.
module tb;
  reg cin, s0; wire o0;
  CARRY4 C (.CIN(cin), .CYINIT(1'b0), .DI0(1'b0), .DI1(1'b0), .DI2(1'b0), .DI3(1'b0),
            .S0(s0), .S1(1'b0), .S2(1'b0), .S3(1'b0), .O0(o0));
  always @(o0) if ($time > 300) $display("O0=%b at %0t", o0, $time);
  initial begin cin = 0; s0 = 0; #1000 s0 = 1; #10 s0 = 0; #190 cin = 1; #2000 $finish; end
endmodule
