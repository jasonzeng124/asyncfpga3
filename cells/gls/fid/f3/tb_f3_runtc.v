// tb_f3_runtc.v -- formal C19 (2026-11-16): a narrow request pulse into a C-element whose other input is already
// asserted.  The C-element is the bd_c2n state LUT exactly as in tb_f3_meta (q = C(r1, ~r2), feedback through an
// FB ps ICBUF, loop FB + 124 ps).  r2 = 0 throughout, so ~r2 = 1 is the "already high" request; r1 pulses high for P
// ps.  Formal's transport model has no pulse shrinkage and its loop then oscillates (period 68-128 ps).  Here: per
// trial, count q's edges in the 8 ns after the pulse and the settled value.  An oscillation = more than 2 edges.
`timescale 1ps/1ps
module tb_f3_runtc;
    parameter integer P = 30, NTRIAL = 200, FB = 300;
    reg r1 = 0, r2 = 0, rst = 1;
    wire q, q_fb;
    SLICE_LUTX #(.INIT(64'h00B2_00B2_00B2_00B2), .META6(1), .TLOOP6(FB + 124), .FB6(6'b000100), .SEED(21)) ustate (
        .A1(r1), .A2(r2), .A3(q_fb), .A4(rst), .A5(1'b0), .A6(1'b0), .O5(), .O6(q));
    ICBUF #(.D(FB)) ufb (.I(q), .O(q_fb));
    integer edges = 0, k, s0 = 0, s1 = 0, sx = 0, osc = 0, maxe = 0;
    always @(q) edges = edges + 1;
    initial begin
        #2000 rst = 0;
        for (k = 0; k < NTRIAL; k = k + 1) begin
            #3000 rst = 1; #1000 rst = 0; #3000;
            edges = 0;
            r1 = 1; #(P) r1 = 0;
            #8000;
            if (edges > maxe) maxe = edges;
            if (edges > 2) osc = osc + 1;
            if (q === 1'b1) s1 = s1 + 1; else if (q === 1'b0) s0 = s0 + 1; else sx = sx + 1;
        end
        $display("RUNTC P=%0d loop=%0d trials=%0d settled0=%0d settled1=%0d X=%0d oscillating(>2 edges)=%0d max_edges=%0d",
                 P, FB + 124, NTRIAL, s0, s1, sx, osc, maxe);
        $finish;
    end
endmodule
