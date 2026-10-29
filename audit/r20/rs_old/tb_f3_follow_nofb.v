// tb_f3_follow.v -- a genuine input pulse right after a runt is not lost
// (audit r16 follow_lost, against the echo-window resolver of 6524fa3..).
//
// NC copies of a C-element LUT (INIT 0x00E8 = maj(a,b,q), A1 = a = 1, A2 = b,
// A3 = q through a 100 ps wire, 100 ps arcs: TLOOP 200), each with its own
// resolver seed.  On b: a 20 ps runt, a 1 ps gap, then a follow pulse W2.
//   W2 = 600 or 200 (>= TLOOP): the node must latch q = 1 in every copy.
//   W2 = 150 (< TLOOP, a runt itself): the node must resolve both ways
//        across the copies (a metastable decision), never stay x.
// The old resolver ignored every change until TLOOP after the runt and lost
// the 200 ps pulse in 40/40 copies; the default (inertial) model latches the
// 150 ps runt in every copy, so it must FAIL the W2 = 150 case.
`timescale 1ps/1ps
module tb_f3_follow;
    localparam integer NC = 40;
    reg b = 0, rst = 1;
    wire [NC-1:0] q, qfb;
    genvar i;
    generate for (i = 0; i < NC; i = i + 1) begin : c
        SLICE_LUTX #(.INIT(64'h0000_0000_0000_00E8), .TA1O6(100), .TA2O6(100), .TA3O6(100),
                     .TA4O6(100), .META6(1), .TLOOP6(200), .SEED(100 + i)) u (
            .A1(1'b1), .A2(b), .A3(qfb[i]), .A4(rst), .A5(1'b0), .A6(1'b0), .O5(), .O6(q[i]));
        ICBUF #(.D(100)) w (.I(q[i]), .O(qfb[i]));
    end endgenerate
    integer fail = 0, n1, n0, nx, k, w2, pass;
    initial begin
        for (pass = 0; pass < 3; pass = pass + 1) begin
            w2 = (pass == 0) ? 600 : (pass == 1) ? 200 : 150;
            rst = 1; b = 0; #3000 rst = 0; #2000;   // INIT 0x00E8 with A4 = 1 reads 0: reset
            b = 1; #20 b = 0; #1 b = 1; #(w2) b = 0;
            #10000;
            n1 = 0; n0 = 0; nx = 0;
            for (k = 0; k < NC; k = k + 1)
                if (q[k] === 1'b1) n1 = n1 + 1; else if (q[k] === 1'b0) n0 = n0 + 1; else nx = nx + 1;
            $display("  W2=%0d: q=1 %0d, q=0 %0d, x %0d of %0d", w2, n1, n0, nx, NC);
            if (w2 >= 200 && n1 != NC) begin
                fail = fail + 1; $display("  FAIL a %0d ps pulse after the runt was lost", w2);
            end
            if (w2 < 200 && (n1 == 0 || n0 == 0 || nx != 0)) begin
                fail = fail + 1; $display("  FAIL a %0d ps follow runt did not resolve both ways", w2);
            end
        end
        if (fail) $display("tb_f3_follow FAIL (%0d)", fail); else $display("tb_f3_follow PASS");
        $finish;
    end
endmodule
