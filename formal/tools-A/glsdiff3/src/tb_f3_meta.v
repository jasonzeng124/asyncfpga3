// tb_f3_meta.v -- metastability, at the prims.v (routed-GLS) level.
//
// A. The bd_arbcell decision element built from SLICE_LUTX exactly as the
//    routed netlist has it: q = C(r1, ~r2) (bd_c2n INIT, rst on A4) fed back
//    through a 300 ps ICBUF, and the fractured grant LUT (bd_arb.v INIT,
//    g1 on O5, g2 on O6) reading q through its own wire.  NTRIAL identical
//    races: reset, r1 rises, r2 rises DT ps later (inside the loop delay),
//    both fall.  The winner is whichever grant the settled q gives.
//    PASS needs both winners to occur, no X on q or a grant once settled,
//    and no settled double grant (an overlap no wider than the O5/O6 arc
//    difference is the structural decode skew tb_arb_overlap measures).
// B. A SLICE_FFX synchroniser with its SDF window (TSU 60 / THD 40): D moves
//    OFFSET ps before CK on every trial.  PASS needs both values captured
//    and Q never X.
// The default prims.v model must FAIL both A and B: it resolves a race the
// same way every time, and a window violation goes X (run_f3.sh checks).
`timescale 1ps/1ps
module tb_f3_meta;
    parameter integer DT = 360, NTRIAL = 200, OFFSET = 20, FB = 300;
    reg r1 = 0, r2 = 0, rst = 1;
    wire q, q_fb, q_g, g1, g2;
    SLICE_LUTX #(.INIT(64'h00B2_00B2_00B2_00B2), .META6(1), .TLOOP6(FB + 124), .SEED(11)) ustate (
        .A1(r1), .A2(r2), .A3(q_fb), .A4(rst), .A5(1'b0), .A6(1'b0), .O5(), .O6(q));
    ICBUF #(.D(FB)) ufb (.I(q), .O(q_fb));
    ICBUF #(.D(FB)) ug  (.I(q), .O(q_g));
    SLICE_LUTX #(.INIT(64'h0C0C_0C0C_A0A0_A0A0),
                 .TA1O5(152), .TA2O5(152), .TA3O5(150), .SEED(12)) ugrant (
        .A1(r1), .A2(r2), .A3(q_g), .A4(1'b0), .A5(1'b0), .A6(1'b1), .O5(g1), .O6(g2));

    integer w1 = 0, w2 = 0, wnone = 0, nx = 0, ndouble = 0, nov = 0, k;
    time tov, wov = 0;
    always @(posedge (g1 & g2)) begin nov = nov + 1; tov = $time; end
    always @(negedge (g1 & g2)) if ($time - tov > wov) wov = $time - tov;

    // B
    reg ck = 0, d = 0;
    wire qf;
    SLICE_FFX #(.TSU(60), .THD(40), .TCKQ(300), .SEED(13)) uff (.CK(ck), .D(d), .CE(1'b1), .SR(1'b0), .Q(qf));
    integer c0 = 0, c1 = 0, cx = 0;
    time tq_max = 0, tck;
    reg cap = 0;
    always @(qf) if (cap && $time - tck > tq_max) tq_max = $time - tck;

    integer fail = 0;
    initial begin
        #2000 rst = 0;
        for (k = 0; k < NTRIAL; k = k + 1) begin
            #3000 rst = 1; #1000 rst = 0; #2000;
            r1 = 1; #(DT) r2 = 1;
            #8000;                          // well past any resolution
            if (q === 1'bx || g1 === 1'bx || g2 === 1'bx) nx = nx + 1;
            if (g1 === 1'b1 && g2 === 1'b1) ndouble = ndouble + 1;
            if (g1 === 1'b1) w1 = w1 + 1; else if (g2 === 1'b1) w2 = w2 + 1; else wnone = wnone + 1;
            r1 = 0; r2 = 0;
        end
        $display("A. %0d races, r2 %0d ps after r1, loop %0d ps: r1 won %0d, r2 won %0d, neither %0d, X %0d, settled double grant %0d",
                 NTRIAL, DT, FB + 124, w1, w2, wnone, nx, ndouble);
        $display("   transient g1&g2 overlaps %0d, widest %0d ps (O5/O6 arc difference 28 ps)", nov, wov);
        if (w1 == 0 || w2 == 0) begin fail = fail + 1; $display("  FAIL A: one side always wins"); end
        if (nx != 0 || ndouble != 0 || wnone != 0) begin fail = fail + 1; $display("  FAIL A: X / double / no grant"); end
        if (wov > 28) begin fail = fail + 1; $display("  FAIL A: overlap wider than the decode skew"); end
        for (k = 0; k < NTRIAL; k = k + 1) begin
            d = 0; #5000 ck = 1; #5000 ck = 0; #5000;        // load 0 cleanly
            #(5000 - OFFSET) d = 1; #(OFFSET) ck = 1; tck = $time; cap = 1; #5000; cap = 0;
            if (qf === 1'b1) c1 = c1 + 1; else if (qf === 1'b0) c0 = c0 + 1; else cx = cx + 1;
            ck = 0;
        end
        $display("B. %0d captures with D %0d ps before CK (window -60/+40): got 1 %0d, got 0 %0d, X %0d; slowest CK->Q %0d ps (nominal 300)",
                 NTRIAL, OFFSET, c1, c0, cx, tq_max);
        if (c0 == 0 || c1 == 0) begin fail = fail + 1; $display("  FAIL B: one value always"); end
        if (cx != 0) begin fail = fail + 1; $display("  FAIL B: X captured"); end
        if (fail) $display("tb_f3_meta FAIL (%0d)", fail); else $display("tb_f3_meta PASS");
        $finish;
    end
endmodule
