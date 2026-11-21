// tb_f3_latch.v -- SLICE_LATX (LDCE/LDPE) delay semantics, self-checking
// against the TRANSPORT expectation: CK/D/CE/SR each reach the storage node one
// arc later (all TCKQ = 300 here: nextpnr's SDF has only CK->Q), and Q is the
// latch function of the delayed pins.  PASS requires GLS_FID; the default
// prims.v model must FAIL (run_f3.sh; the negative control).
//   L1  latch open, 50 ps D pulse at 1000: passes as a 50 ps Q pulse at 1300
//   L2  latch open, D 1->0 at 2000, back to 1 at 2120, 0 at 2130: three Q
//       edges, the last at 2430 (not early)
//   L3  latch open, D rises at 3000 and the gate closes at 3040: Q captures the
//       new D at 3300 and holds it after the close lands at 3340
//   L4  latch closed holding 1 (LDCE), 40 ps async clear pulse at 4000: Q
//       falls at 4300 and stays 0 (the clear wins, the gate is closed)
//   L5  latch closed, D pulses 5000-5100: no Q edge
`timescale 1ps/1ps
module tb_f3_latch;
    reg g = 1, d = 0, sr = 0;
    wire q;
    SLICE_LATX #(.INIT(1'b0), .SRVAL(1'b0), .GHIGH(1'b1), .TCKQ(300)) ul (
        .CK(g), .D(d), .CE(1'b1), .SR(sr), .Q(q));

    integer n1 = 0, n2 = 0, n3 = 0, n4 = 0, n5 = 0;
    time t1a = 0, t1b = 0, t2 = 0, t3 = 0, t4 = 0;
    always @(q) begin
        $display("  q t=%0d %b", $time, q);
        if ($time >= 1000 && $time < 2000) begin n1 = n1 + 1; if (n1 == 1) t1a = $time; if (n1 == 2) t1b = $time; end
        if ($time >= 2000 && $time < 3000) begin n2 = n2 + 1; t2 = $time; end
        if ($time >= 3000 && $time < 4000) begin n3 = n3 + 1; t3 = $time; end
        if ($time >= 4000 && $time < 5000) begin n4 = n4 + 1; t4 = $time; end
        if ($time >= 5000) n5 = n5 + 1;
    end
    reg q3a = 1'bx, q3b = 1'bx, q4 = 1'bx;
    initial begin
        #1000 d = 1; #50 d = 0;                       // L1
        #950  d = 1;                                  // 2000: d 0->1 (q follows, L2 starts at 1)
        #120  d = 0; #10 d = 1;                       // 2120 fall, 2130 rise
        #370  d = 0;                                  // 2500: settle q to 0 before L3 (lands 2800)
        #500  d = 1; #40 g = 0;                       // 3000 d rise, 3040 close
        #200  d = 0;                                  // 3240: closed, must not reach q
        #760  sr = 1; #40 sr = 0;                     // 4000-4040 clear pulse
        #960  d = 1; #100 d = 0;                      // 5000-5100 closed, no edge
    end
    initial begin #3500 q3a = q; #400 q3b = q; #700 q4 = q; end

    integer fail = 0;
    task chk(input c, input [8*72-1:0] what);
        begin if (!c) begin fail = fail + 1; $display("  FAIL %0s", what); end
              else $display("  ok   %0s", what); end
    endtask
    initial begin
        #7000;
        $display("L1: %0d edges at %0d, %0d (transport: 2, 1300 and 1350)", n1, t1a, t1b);
        chk(n1 == 2 && t1a == 1000 + 300 && t1b == 1050 + 300, "L1 50 ps D pulse through an open latch");
        // edges in [2000,3000): 2300 (rise), 2420 (fall), 2430 (rise), 2800 (the 2500 fall)
        $display("L2: %0d edges, last %0d (transport: 4, 2300 2420 2430 2800)", n2, t2);
        chk(n2 == 4 && t2 == 2500 + 300, "L2 D 2120/2130 edges both reach Q (2420, 2430)");
        $display("L3: %0d edges, last %0d, q at 3500 = %b, at 3900 = %b (transport: 1 edge 3300, 1, 1)", n3, t3, q3a, q3b);
        chk(n3 == 1 && t3 == 3000 + 300 && q3a === 1'b1 && q3b === 1'b1, "L3 D 40 ps before close is captured");
        $display("L4: %0d edges, last %0d, q at 4600 = %b (transport: 1, 4300, 0)", n4, t4, q4);
        chk(n4 == 1 && t4 == 4000 + 300 && q4 === 1'b0, "L4 40 ps async clear lands and holds");
        chk(n5 == 0, "L5 closed latch: D pulse gives no edge");
        if (fail) $display("tb_f3_latch FAIL (%0d)", fail); else $display("tb_f3_latch PASS");
        $finish;
    end
endmodule
