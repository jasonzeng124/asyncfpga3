`timescale 1ps/1ps
// Auditor tb (r8): narrow pulses through CARRY4 and SLICE_LATX.
// CARRY4 O0 = S0 ^ CIN (S0->O0 arc 223). S0 pulses of 29 ps and 99 ps.
// Transport: O0 pulse at +223 of the same width. CO3 via S0 (340/433/514/489 for CO0..3),
// set S1..S3=1 so CO3 = S0?CIN:DI0 -> with CIN=1, DI0=0 a S0 pulse gives CO3 pulse at +489.
// SLICE_LATX open (CK=1, CE=1): D pulse of 29/99 ps -> Q pulse at +TCKQ(100).
module tb;
  reg cin, s0, s123; wire o0, co3;
  CARRY4 C (.CIN(cin), .CYINIT(1'b0), .DI0(1'b0), .DI1(1'b0), .DI2(1'b0), .DI3(1'b0),
            .S0(s0), .S1(s123), .S2(s123), .S3(s123), .O0(o0), .CO3(co3));
  reg ck, d, ce, sr; wire ql;
  SLICE_LATX #(.INIT(1'b0), .GHIGH(1'b1), .TCKQ(100)) L (.CK(ck), .D(d), .CE(ce), .SR(sr), .Q(ql));
  always @(o0)  if ($time > 300) $display("O0=%b at %0t", o0, $time);
  always @(co3) if ($time > 300) $display("CO3=%b at %0t", co3, $time);
  always @(ql)  if ($time > 300) $display("LQ=%b at %0t", ql, $time);
  initial begin
    cin = 0; s0 = 0; s123 = 0; ck = 1; ce = 1; sr = 0; d = 0;
    #1000 s0 = 1; #29 s0 = 0;            // 29 ps S0 pulse at 1000 -> O0 1223..1252
    #1971 s0 = 1; #99 s0 = 0;            // 99 ps at 3000 -> O0 3223..3322
    #1901 s123 = 1; cin = 1;              // 5000: O0 = 1 (cin), CO3 = S0?1:0
    #1000 s0 = 1; #29 s0 = 0;            // 6000: CO3 pulse 6489..6518, O0 low pulse 6223..6252
    #1971 s0 = 1; #99 s0 = 0;            // 8000: CO3 pulse 8489..8588
    #1901 d = 1; #29 d = 0;               // 10000: LQ pulse 10100..10129
    #1971 d = 1; #99 d = 0;               // 12000: LQ pulse 12100..12199
    #1901 $finish;
  end
endmodule
