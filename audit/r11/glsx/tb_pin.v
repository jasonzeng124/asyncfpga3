`timescale 1ps/1ps
// Auditor tb (r11): SLICE_FFX fid pin transport arcs and external CK->Q.
module tb;
  reg ck=0, d=0, one=1, zero=0; wire q0, q1, q2;
  // default arcs: CK->Q must be exactly TCKQ
  SLICE_FFX #(.TCKQ(340), .TSU(100), .THD(100)) a (.CK(ck), .D(d), .CE(one), .SR(zero), .Q(q0));
  // D arc 300 ps: a D change 250 ps before CK reaches the node 50 ps AFTER it
  SLICE_FFX #(.TCKQ(340), .TSU(20), .THD(20), .TDI(300)) b (.CK(ck), .D(d), .CE(one), .SR(zero), .Q(q1));
  // D arc 300 ps, narrow D pulse 30 ps well before CK: transport keeps it
  reg dp=0; wire q2n;
  SLICE_FFX #(.TCKQ(340), .TSU(20), .THD(20), .TDI(300)) c (.CK(ck), .D(dp), .CE(one), .SR(zero), .Q(q2));
  always @(q0) $display("q0=%b at %0t", q0, $time);
  always @(q1) $display("q1=%b at %0t", q1, $time);
  always @(q2) $display("q2=%b at %0t", q2, $time);
  initial begin
    #1000 d = 1; #250 ck = 1; $display("CK rise at %0t (D rose 250 before)", $time);
    #1000 ck = 0; #1000 ck = 1; $display("CK rise at %0t", $time); #1000 ck = 0;
    #1000; dp = 1; #30 dp = 0; #250 ck = 1; $display("CK rise at %0t (dp 30ps pulse ended 250 before, node sees it 20..50 after CK)", $time);
    #1000 ck = 0; #1000 $finish;
  end
endmodule
