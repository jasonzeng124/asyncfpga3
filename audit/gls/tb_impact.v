// Audit tb: bundled-data impact of sample-at-fire LUT paths.
// Data cone: one XOR3 LUT (INIT 0x96, all arcs 124 ps, research SLICE_LUTX).
// Its inputs change at 1000 (A1), 1040 (A2), 1100 (A3): f goes 0->1->0->1.
// Correct final value 1.  The "request" is a capture edge at time TCAP on a
// research SLICE_FFX (TSU=0, TCKQ=100).  Reference: the same function through
// an explicit TRANSPORT 124 ps delay, and through a Verilog continuous-assign
// (inertial) 124 ps delay, each captured the same way.
`timescale 1ps/1ps
module tb;
    parameter TCAP = 1200;
    reg a1 = 0, a2 = 0, a3 = 0, ck = 0;
    wire o_gls;
    SLICE_LUTX #(.INIT(64'h96)) lut (.A1(a1), .A2(a2), .A3(a3), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o_gls));
    wire f = a1 ^ a2 ^ a3;
    reg o_tr = 0;  always @(f) o_tr <= #124 f;      // transport reference
    wire #124 o_in = f;                             // inertial reference
    wire q_gls, q_tr, q_in;
    SLICE_FFX ff_gls (.CK(ck), .D(o_gls), .CE(1'b1), .SR(1'b0), .Q(q_gls));
    SLICE_FFX ff_tr  (.CK(ck), .D(o_tr),  .CE(1'b1), .SR(1'b0), .Q(q_tr));
    SLICE_FFX ff_in  (.CK(ck), .D(o_in),  .CE(1'b1), .SR(1'b0), .Q(q_in));
    always @(o_gls) $display("t=%0d o_gls=%b", $time, o_gls);
    always @(o_tr)  $display("t=%0d o_transport=%b", $time, o_tr);
    always @(o_in)  $display("t=%0d o_inertial=%b", $time, o_in);
    initial begin
        #1000 a1 = 1; #40 a2 = 1; #60 a3 = 1;
    end
    initial begin #TCAP ck = 1; end
    initial #2000 begin
        $display("TCAP=%0d captured: gls=%b transport=%b inertial=%b (correct=1)", TCAP, q_gls, q_tr, q_in);
        $finish;
    end
endmodule
