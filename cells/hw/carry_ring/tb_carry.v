// tb_carry.v -- event-driven GLS of carry_ro_top's group 0 on the netlist
// decoded from the bitstream (cells/gls/fid/fasm2net.py -> gen.py), with the
// prjxray delays re-keyed onto it.  Group 0 holds one ring of every kind
// (KIND[(0+b)%8]: L8 C1 C4 F8 C16 L16 C32 F16).
//
// BSCAN is prims.v's passive stub, so hold stays at its power-on 0 and group 0
// is the selected group.  Every ring LUT starts X, and ~X is X, so the rings
// are first PARKED: hold[9] (a group bit) is forced to 1 for 40 ns, which
// selects group 8 (no ring) -- en = 0 everywhere, each NAND drives 1 and the
// chain fills with defined values -- then released, which is exactly the
// board's "select the group" step.  Nothing else is touched.
//
// Reports, per slot b, the mean period of ring_fb[b] (the NAND output, the node
// the slot mux taps) over the rising edges after WARM ns, as
//     RING <b> <period_ps> <edges>
`timescale 1ps/1ps
module tb_carry;
    top dut ();
    `include "carry_signals.vh"   // `HOLD9, `FB0..`FB7 (carry_gls.sh writes it)

    integer tend, warm;
    integer n [0:7];
    time t0 [0:7];
    time t1 [0:7];
    wire [7:0] fb = {`FB7, `FB6, `FB5, `FB4, `FB3, `FB2, `FB1, `FB0};
    integer k;

    initial begin
        tend = 3000; warm = 200;
        if ($value$plusargs("TEND=%d", tend)) ;
        if ($value$plusargs("WARM=%d", warm)) ;
        for (k = 0; k < 8; k = k + 1) begin n[k] = 0; t0[k] = 0; t1[k] = 0; end
        force `HOLD9 = 1'b1;
        #40000;
        release `HOLD9;
        #(tend * 1000);
        for (k = 0; k < 8; k = k + 1)
            if (n[k] > 1)
                $display("RING %0d %0d %0d", k, (t1[k] - t0[k]) / (n[k] - 1), n[k]);
            else
                $display("RING %0d DEAD %0d", k, n[k]);
        $finish;
    end

    genvar gb;
    generate for (gb = 0; gb < 8; gb = gb + 1) begin : mon
        always @(posedge fb[gb]) if ($time > warm * 1000) begin
            if (n[gb] == 0) t0[gb] = $time;
            t1[gb] = $time;
            n[gb] = n[gb] + 1;
        end
    end endgenerate
endmodule
