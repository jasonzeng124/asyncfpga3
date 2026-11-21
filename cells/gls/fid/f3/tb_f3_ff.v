// tb_f3_ff.v -- SLICE_FFX and BUFGCTRL pin semantics (S6), self-checking
// against the TRANSPORT + minimum-pulse-width expectation.  PASS requires
// GLS_FID; the default prims.v model must FAIL (run_f3.sh; the negative
// control).  TCKQ = 300 everywhere; the fid TMPW band is the default 70 +- 20.
//   F1  CK high 120 ps (wider than the band, narrower than CK->Q), the next
//       rise 240 ps after the first: the runt clocks the flop, and Q makes a
//       240 ps pulse 1300-1540 (both edges, transport CK->Q)
//   F2  CK high 30 ps (below the band): no capture, no Q edge
//   F3  CK high 70 ps (the band centre), 200 trials: both outcomes occur, X 0
//   F4  pin arcs 100 ps: a 40 ps SR pulse (narrower than its arc) straddling
//       a rise resets Q (1300), the next rise 200 ps later sets it (1500),
//       and one more (D 0) clears it (1800)
//   F5  pin arcs 100 ps: CE dips 1990-2010 around the rise at 2000 (a CE edge
//       20 ps after another): that edge holds; rises at 2200 and 2400 give Q
//       1 at 2500 and 0 at 2700, and no edge at 2300
//   F6  SR (SDF window -40/+40) rises 10 ps before CK, 200 trials: SR is in
//       the aperture, so both outcomes occur, X 0
//   F7  TSRI 200 vs TCKI 1: SR rising 50 ps before CK reaches the node after
//       it, so that edge loads D (Q 1 at 1300)
//   G1  BUFGCTRL TI0O 200: a 120 ps I0 pulse comes out (O 1200-1320) and
//       clocks the flop behind it (Q 1 at 1500)
`timescale 1ps/1ps
module tb_f3_ff;
    parameter integer NTRIAL = 200;
    integer fail = 0;
    task chk(input c, input [8*80-1:0] what);
        begin if (!c) begin fail = fail + 1; $display("  FAIL %0s", what); end
              else $display("  ok   %0s", what); end
    endtask

    // ---- F1, F2
    reg cka = 0, da = 0;
    wire qa;
    SLICE_FFX #(.TCKQ(300), .SEED(3)) ua (.CK(cka), .D(da), .CE(1'b1), .SR(1'b0), .Q(qa));
    integer na1 = 0, na2 = 0; time ta1a = 0, ta1b = 0;
    always @(qa) if ($time > 0) begin
        $display("  qa t=%0d %b", $time, qa);
        if ($time >= 1000 && $time < 2500) begin na1 = na1 + 1; if (na1 == 1) ta1a = $time; else ta1b = $time; end
        if ($time >= 2500 && $time < 6000) na2 = na2 + 1;
    end
    initial begin
        #500 da = 1; #500 cka = 1; #120 cka = 0; #60 da = 0; #60 cka = 1;   // 1000, 1120, 1180, 1240
        #500 cka = 0;                                                       // 1740
        #1000 da = 1; #260 cka = 1; #30 cka = 0;                            // 3000-3030 runt
    end

    // ---- F3
    reg ck3 = 0, d3 = 0;
    wire q3;
    SLICE_FFX #(.TCKQ(300), .SEED(5)) u3 (.CK(ck3), .D(d3), .CE(1'b1), .SR(1'b0), .Q(q3));
    integer c31 = 0, c30 = 0, c3x = 0;

    // ---- F4, F5
    reg ckb = 0, db = 1, ceb = 1, srb = 0;
    wire qb;
    // the pin arcs are GLS_FID-only parameters (the default prims.v must stay
    // byte-identical), so the default run gets the same flop without them
    SLICE_FFX #(.INIT(1'b1), .SRVAL(1'b0), .TCKQ(300), .TSU(5), .THD(5), .SEED(7)
`ifdef GLS_FID
                , .TCKI(100), .TDI(100), .TCEI(100), .TSRI(100)
`endif
                ) ub (
        .CK(ckb), .D(db), .CE(ceb), .SR(srb), .Q(qb));
    integer nb4 = 0, nb5 = 0; time tb4a = 0, tb4b = 0, tb4c = 0, tb5a = 0, tb5b = 0;
    reg qb4a, qb4b, qb4c, qb5a, qb5b;
    always @(qb) if ($time > 0) begin
        $display("  qb t=%0d %b", $time, qb);
        if ($time >= 1000 && $time < 1900) begin nb4 = nb4 + 1; if (nb4 == 1) begin tb4a = $time; qb4a = qb; end else if (nb4 == 2) begin tb4b = $time; qb4b = qb; end else begin tb4c = $time; qb4c = qb; end end
        if ($time >= 1900 && $time < 4000) begin nb5 = nb5 + 1; if (nb5 == 1) begin tb5a = $time; qb5a = qb; end else begin tb5b = $time; qb5b = qb; end end
    end
    initial begin
        #970 srb = 1; #30 ckb = 1; #10 srb = 0;          // 970-1010 SR, rise 1000 -> 0 at 1300
        #90 ckb = 0; #100 ckb = 1;                       // 1100 fall, 1200 rise (D=1) -> 1 at 1500
        #100 ckb = 0; db = 0;                            // 1300
        #200 ckb = 1; #100 ckb = 0;                      // 1500 rise (D=0) -> 0 at 1800
        #290 db = 1;                                     // 1890: D = 1 for F5
        #100 ceb = 0; #10 ckb = 1; #10 ceb = 1;          // 1990 CE dip, 2000 rise, 2010 CE back
        #90 ckb = 0; #100 ckb = 1;                       // 2100, 2200 rise (CE=1 D=1) -> 1 at 2500
        #50 db = 0; #50 ckb = 0; #100 ckb = 1;           // 2250 D=0, 2300, 2400 rise -> 0 at 2700
        #100 ckb = 0;                                    // 2500
    end

    // ---- F6
    reg ck6 = 0, sr6 = 0;
    wire q6;
    SLICE_FFX #(.INIT(1'b1), .SRVAL(1'b0), .TCKQ(300), .TSU(40), .THD(40), .SEED(9)) u6 (
        .CK(ck6), .D(1'b1), .CE(1'b1), .SR(sr6), .Q(q6));
    integer c61 = 0, c60 = 0, c6x = 0;

    // ---- F7
    reg ck7 = 0, sr7 = 0;
    wire q7;
    SLICE_FFX #(.INIT(1'b0), .SRVAL(1'b0), .TCKQ(300), .TSU(5), .THD(5), .SEED(11)
`ifdef GLS_FID
                , .TCKI(1), .TSRI(200)
`endif
                ) u7 (.CK(ck7), .D(1'b1), .CE(1'b1), .SR(sr7), .Q(q7));
    reg q7a;
    initial begin #950 sr7 = 1; #50 ck7 = 1; #400 ck7 = 0; #100 q7a = q7; #100 sr7 = 0; end

    // ---- G1
    reg ig = 0;
    wire og, qg;
    BUFGCTRL #(.TI0O(200)) ug (.I0(ig), .I1(1'b0), .S0(1'b0), .S1(1'b0), .CE0(1'b1), .CE1(1'b1),
                               .IGNORE0(1'b1), .IGNORE1(1'b1), .O(og));
    SLICE_FFX #(.TCKQ(300), .SEED(13)) ugf (.CK(og), .D(1'b1), .CE(1'b1), .SR(1'b0), .Q(qg));
    integer ng = 0; time tga = 0, tgb = 0, tq = 0;
    always @(og) if ($time > 500) begin ng = ng + 1; if (ng == 1) tga = $time; else tgb = $time; end
    always @(qg) if ($time > 0 && qg === 1'b1 && tq == 0) tq = $time;
    initial begin #1000 ig = 1; #120 ig = 0; end

    integer k;
    initial begin
        #8000;
        $display("F1: %0d qa edges at %0d, %0d (transport: 2, 1300 and 1540)", na1, ta1a, ta1b);
        chk(na1 == 2 && ta1a == 1300 && ta1b == 1540, "F1 120 ps CK runt clocks; 240 ps Q pulse kept");
        $display("F2: %0d qa edges after a 30 ps CK runt (MPW model: 0)", na2);
        chk(na2 == 0, "F2 CK runt below the minimum pulse width does not clock");
        $display("F4: %0d qb edges, %0d->%b, %0d->%b, %0d->%b (transport: 3, 1300->0, 1500->1, 1800->0)", nb4, tb4a, qb4a, tb4b, qb4b, tb4c, qb4c);
        chk(nb4 == 3 && tb4a == 1300 && qb4a === 1'b0 && tb4b == 1500 && qb4b === 1'b1 && tb4c == 1800 && qb4c === 1'b0,
            "F4 40 ps SR pulse through a 100 ps arc resets; next edge 200 ps on sets");
        $display("F5: %0d qb edges, %0d->%b, %0d->%b (transport: 2, 2500->1, 2700->0)", nb5, tb5a, qb5a, tb5b, qb5b);
        chk(nb5 == 2 && tb5a == 2500 && qb5a === 1'b1 && tb5b == 2700 && qb5b === 1'b0,
            "F5 CE edge 20 ps after another: the dip holds, later edges both reach Q");
        $display("F7: q at 1500 = %b (SR arc 200 > CK arc 1: the edge loads D = 1)", q7a);
        chk(q7a === 1'b1, "F7 SR delayed by its own arc misses the edge");
        $display("G1: %0d BUFG O edges at %0d, %0d (transport: 2, 1200 and 1320); flop Q 1 at %0d (1500)", ng, tga, tgb, tq);
        chk(ng == 2 && tga == 1200 && tgb == 1320 && tq == 1500, "G1 120 ps pulse through a 200 ps BUFG clocks the flop");

        // F3: 70 ps runts
        for (k = 0; k < NTRIAL; k = k + 1) begin
            d3 = 0; #1000 ck3 = 1; #1000 ck3 = 0; #1000;   // load 0 cleanly
            d3 = 1; #1000 ck3 = 1; #70 ck3 = 0; #2000;
            if (q3 === 1'b1) c31 = c31 + 1; else if (q3 === 1'b0) c30 = c30 + 1; else c3x = c3x + 1;
        end
        $display("F3: %0d CK runts of 70 ps (band 50..90): got 1 %0d, got 0 %0d, X %0d", NTRIAL, c31, c30, c3x);
        chk(c31 > 0 && c30 > 0 && c3x == 0, "F3 runt at the minimum pulse width resolves either way, no X");

        // F6: SR into the aperture
        for (k = 0; k < NTRIAL; k = k + 1) begin
            sr6 = 0; #1000 ck6 = 1; #1000 ck6 = 0; #1000;  // load 1 cleanly
            #990 sr6 = 1; #10 ck6 = 1; #1000 ck6 = 0; #1000;
            if (q6 === 1'b1) c61 = c61 + 1; else if (q6 === 1'b0) c60 = c60 + 1; else c6x = c6x + 1;
        end
        $display("F6: %0d SR rises 10 ps before CK (window -40/+40): got 1 %0d, got 0 %0d, X %0d", NTRIAL, c61, c60, c6x);
        chk(c61 > 0 && c60 > 0 && c6x == 0, "F6 SR change in the aperture resolves either way, no X");

        if (fail) $display("tb_f3_ff FAIL (%0d)", fail); else $display("tb_f3_ff PASS");
        $finish;
    end
endmodule
