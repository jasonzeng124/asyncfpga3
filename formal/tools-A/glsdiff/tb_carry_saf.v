// tb_carry_saf.v -- is CARRY4 (and the latch's D->Q) still "sample at fire" under GLS_FID?
// CARRY4: CIN=CYINIT=0, DI=0, so O0 = S0 with arc TS0O0 = 223 ps (prims.v default).
// S0: pulse 1000-1010, then rises at 1200 and stays.  Per-pin transport (Lean Pure,
// lo=hi=223): O0 pulse 1223-1233, final rise at 1423.  SAF: the 1000 change fires at
// 1223 and copies S0(1223)=1, so O0 rises at 1223 -- 23 ps after its cause at 1200.
// Latch (open, D->Q 100 ps): D pulse 3000-3010, rise at 3060: transport 3100-3110 and
// 3160; SAF rise at 3100 (40 ps after its cause).
`timescale 1ps/1ps
module tb_carry_saf;
    reg s0 = 0, d = 0;
    wire o0, o1, o2, o3, c0, c1, c2, c3, lq;
    CARRY4 uc (.CIN(1'b0), .CYINIT(1'b0), .DI0(1'b0), .DI1(1'b0), .DI2(1'b0), .DI3(1'b0),
               .S0(s0), .S1(1'b0), .S2(1'b0), .S3(1'b0),
               .O0(o0), .O1(o1), .O2(o2), .O3(o3), .CO0(c0), .CO1(c1), .CO2(c2), .CO3(c3));
    SLICE_LATX #(.INIT(1'b0), .GHIGH(1'b1), .TCKQ(100)) ul (.CK(1'b1), .D(d), .CE(1'b1), .SR(1'b0), .Q(lq));
    always @(o0) if ($time > 500) $display("O0 %0d %b", $time, o0);
    always @(lq) if ($time > 500) $display("LQ %0d %b", $time, lq);
    initial begin
        #1000 s0 = 1; #10 s0 = 0; #190 s0 = 1;
        #1800 d = 1; #10 d = 0; #50 d = 1;
        #2000 $finish;
    end
endmodule
