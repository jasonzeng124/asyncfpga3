// tb_f3_arbm.v -- routed GLS of hw/arb_mtbf (six bd_c2n_set decision elements
// on two free-running rings, plus sync1/sync2 flop synchronizers), for the
// F3 metastability model.  Signal names come from arbm_sig.vh, generated
// from this route's nets.map by run_f3.sh.  It reports; run_f3.sh judges.
`timescale 1ps/1ps
`include "arbm_sig.vh"
module tb_f3_arbm;
    top dut ();
    integer tend_ns = 40000;
    initial begin
        if ($value$plusargs("TEND=%d", tend_ns)) ;
        force `R1 = 1'b0; force `R2 = 1'b0; force `RING3 = 1'b0;
        #30000;
        release `R1; release `R2; release `RING3;
    end
    // grant overlap per channel (g1c & g2c, the raw anomaly)
    integer nov[0:5], ngr1[0:5], ngr2[0:5], nq[0:5];
    time tov[0:5], wmax[0:5];
    integer i;
    initial for (i = 0; i < 6; i = i + 1) begin nov[i] = 0; wmax[i] = 0; ngr1[i] = 0; ngr2[i] = 0; nq[i] = 0; end
    `define CHMON(k, G1, G2, Q) \
        always @(posedge (G1 & G2)) if ($time > 60000) begin nov[k] = nov[k] + 1; tov[k] = $time; end \
        always @(negedge (G1 & G2)) if ($time > 60000 && nov[k] > 0 && $time - tov[k] > wmax[k]) wmax[k] = $time - tov[k]; \
        always @(posedge G1) if ($time > 60000) ngr1[k] = ngr1[k] + 1; \
        always @(posedge G2) if ($time > 60000) ngr2[k] = ngr2[k] + 1; \
        always @(Q) if ($time > 60000) nq[k] = nq[k] + 1;
    `CHMON(0, `G1_0, `G2_0, `Q_0)
    `CHMON(1, `G1_1, `G2_1, `Q_1)
    `CHMON(2, `G1_2, `G2_2, `Q_2)
    `CHMON(3, `G1_3, `G2_3, `Q_3)
    `CHMON(4, `G1_4, `G2_4, `Q_4)
    `CHMON(5, `G1_5, `G2_5, `Q_5)
    integer nx = 0, nr1 = 0, nr2 = 0;
    time tr1a = 0, tr1b = 0, tr2a = 0, tr2b = 0;
    always @(posedge `R1) if ($time > 60000) begin if (nr1 == 0) tr1a = $time; tr1b = $time; nr1 = nr1 + 1; end
    always @(posedge `R2) if ($time > 60000) begin if (nr2 == 0) tr2a = $time; tr2b = $time; nr2 = nr2 + 1; end
    always @(`G1_0 or `G2_0) if ($time > 60000 && (`G1_0 === 1'bx || `G2_0 === 1'bx)) nx = nx + 1;
    initial begin
        #(tend_ns * 1000);
        for (i = 0; i < 6; i = i + 1)
            $display("CH %0d grants g1=%0d g2=%0d overlaps=%0d widest=%0d ps, q edges %0d", i, ngr1[i], ngr2[i], nov[i], wmax[i], nq[i]);
        $display("X on ch0 grants after settle: %0d", nx);
        if (nr1 > 1 && nr2 > 1)
            $display("RING r1 period %0d ps, r2 period %0d ps", (tr1b - tr1a) / (nr1 - 1), (tr2b - tr2a) / (nr2 - 1));
        $display("ARBM_DONE t=%0t", $time);
        $finish;
    end
endmodule
