`timescale 1ps/1ps
// Auditor tb: X behaviour of research prims.v SLICE_LATX / SLICE_FFX, and
// SAF vs transport on CARRY4 O0.
module tb;
  reg ck, d, ce, sr;
  wire ql, qf;
  SLICE_LATX #(.INIT(1'b0), .GHIGH(1'b1), .TCKQ(100)) L (.CK(ck), .D(d), .CE(ce), .SR(sr), .Q(ql));
  SLICE_FFX  #(.INIT(1'b0), .TCKQ(100)) F (.CK(ck), .D(d), .CE(ce), .SR(sr), .Q(qf));
  reg cin, s0; wire o0;
  CARRY4 C (.CIN(cin), .CYINIT(1'b0), .DI0(1'b0), .DI1(1'b0), .DI2(1'b0), .DI3(1'b0),
            .S0(s0), .S1(1'b0), .S2(1'b0), .S3(1'b0), .O0(o0));
  always @(o0) if ($time > 0) $display("CARRY O0=%b at %0t", o0, $time);
  initial begin
    ck = 0; d = 0; ce = 0; sr = 0; cin = 0; s0 = 0;
    #1000;
    // L1: latch closed by CE=0, CK goes X, D=1: silicon holds 0
    d = 1; ce = 0; ck = 1'bx; #500 $display("L1 CK=x CE=0 D=1 (closed by CE): Q=%b  (expect 0)", ql);
    ck = 0; d = 0; #500;
    // L2: CK=0 (closed), CE=x, D=1
    d = 1; ce = 1'bx; #500 $display("L2 CK=0 CE=x D=1 (closed by CK): Q=%b  (expect 0)", ql);
    ce = 0; d = 0; #500;
    // L3: CK=x, CE=x, SR=0, D=1 -- genuinely unknown (x expected)
    d = 1; ck = 1'bx; ce = 1'bx; #500 $display("L3 CK=x CE=x D=1: Q=%b  (expect x)", ql);
    ck = 0; ce = 0; d = 0; #500;
    // flop: Q=0 now (never clocked). F1: SR=x, CE=1, D=1, posedge -> 1 or 0? unknown => x
    sr = 1'bx; ce = 1; d = 1; #200 ck = 1; #300 $display("F1 SR=x CE=1 D=1 posedge: Q=%b  (expect x)", qf);
    ck = 0; sr = 1; #200 ck = 1; #300 ck = 0; sr = 0; #200 $display("   reset Q=%b", qf);
    // F2: CE=x, D=1, Q=0, posedge -> x
    ce = 1'bx; d = 1; #200 ck = 1; #300 $display("F2 SR=0 CE=x D=1 Q=0 posedge: Q=%b  (expect x)", qf);
    ck = 0; ce = 0; #500;
    // CARRY4 O0 = S0 ^ CIN.  S0 rises at t0 (arc 223), CIN rises at t0+30 (arc 222).
    // transport: O0 rises t0+223, falls t0+30+222 = t0+252.
    $display("CARRY t0=%0t  transport expects O0 1 @%0t, 0 @%0t", $time, $time+223, $time+252);
    s0 = 1; #30 cin = 1; #1000;
    // S0 falls at t1 (223) then CIN falls at t1+100 (222): transport 1? O0 = S0^CIN:
    // t1: 1^1 -> 0^1 = 1 (rise t1+223); t1+100: 0^0 = 0 (fall t1+322)
    $display("CARRY t1=%0t  transport expects O0 1 @%0t, 0 @%0t", $time, $time+223, $time+322);
    s0 = 0; #100 cin = 0; #1000;
    $finish;
  end
endmodule
