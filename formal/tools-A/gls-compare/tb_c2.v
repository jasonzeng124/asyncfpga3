// tb_c2.v -- bd_c2 (C-element, INIT 64'h00E8_00E8_00E8_00E8) on the research
// GLS's SLICE_LUTX, q fed back to I2 (physical A3), rst on A4.
// Pins: A1 = a, A2 = b, A3 = q (feedback), A4 = rst, A5 = A6 = 0.
// Knobs: `LUTMOD (SLICE_LUTX | LUT_TRC), `TA1 `TA2 `TA3 (per-pin O6 arcs,
// default nextpnr's flat 124), `FB (feedback ICBUF delay; 0 = direct, the
// intra-site 0 ps route ARBITER.md reports; build with -DGLS_TRANSPORT_IC
// for the baked build's transport wire).
// Output lines:
//   S <a> <b> <q> <pin> <ntrans> <final q>     single-input flip from a stable state
//   K <q0> <skew> <ntrans> <final q> <late>    a,b 01->10; a moves at T, b at T+skew;
//                                              late = transitions in the last 1 ns
`timescale 1ps/1ps
`ifndef LUTMOD
 `define LUTMOD SLICE_LUTX
`endif
`ifndef TA1
 `define TA1 124
`endif
`ifndef TA2
 `define TA2 124
`endif
`ifndef TA3
 `define TA3 124
`endif
`ifndef FB
 `define FB 0
`endif
module tb_c2;
    reg a = 0, b = 0, rst = 1;
    wire q, qf;
    `LUTMOD #(.INIT(64'h00E8_00E8_00E8_00E8), .TA1O6(`TA1), .TA2O6(`TA2), .TA3O6(`TA3))
        c (.A1(a), .A2(b), .A3(qf), .A4(rst), .A5(1'b0), .A6(1'b0), .O6(q), .O5());
    generate if (`FB > 0) begin : gfb
        ICBUF #(.D(`FB)) ic (.I(q), .O(qf));
    end else begin : gd
        assign qf = q;
    end endgenerate

    integer n, nl; time tlate;
    always @(q) begin n = n + 1; if ($time >= tlate) nl = nl + 1; end

    task settle_to(input reg qa, input reg qb, input reg want_q);
        begin
            // reset, then drive to a stable state with the requested q
            rst = 1; a = 0; b = 0; #2000; rst = 0; #1000;
            if (want_q) begin a = 1; b = 1; #2000; end
            a = qa; b = qb; #2000;
        end
    endtask

    integer s, q0, pa, pb, pq, pin;
    initial begin
        tlate = 64'hFFFF_FFFF_FFFF;
        // single-input flips from every stable state
        for (pq = 0; pq < 2; pq = pq + 1)
          for (pa = 0; pa < 2; pa = pa + 1)
            for (pb = 0; pb < 2; pb = pb + 1)
              if (pa != pb || pa == pq)
                for (pin = 0; pin < 3; pin = pin + 1) begin
                    settle_to(pa, pb, pq);
                    if (q !== pq) $display("SETUP_FAIL %0d%0d%0d q=%b", pa, pb, pq, q);
                    n = 0;
                    if (pin == 0) a = !a; else if (pin == 1) b = !b; else rst = 1;
                    #3000;
                    $display("S %0d %0d %0d %0d %0d %b", pa, pb, pq, pin, n, q);
                end
        // opposite-sense double change a,b: 01 -> 10, swept skew
        for (q0 = 0; q0 < 2; q0 = q0 + 1)
            for (s = -300; s <= 300; s = s + 1) begin
                settle_to(0, 1, q0);
                n = 0; nl = 0;
                if (s >= 0) begin a = 1; #(s) b = 0; end
                else begin b = 0; #(-s) a = 1; end
                tlate = $time + 9000;
                #10000;
                tlate = 64'hFFFF_FFFF_FFFF;
                $display("K %0d %0d %0d %b %0d", q0, s, n, q, nl);
            end
        $finish;
    end
endmodule

// Transport-delay reference (formal Core/Delay/Pure with lo = hi): zero-time
// mux tree, then a pure delay.  The delay is the arc of the pin that changed
// last, like the GLS's specify block; NOT a GLS primitive.
module LUT_TRC (input wire A1, A2, A3, A4, A5, A6, output wire O5, O6);
    parameter [63:0] INIT = 64'h0;
    parameter TA1O6 = 124, TA2O6 = 124, TA3O6 = 124;
    // the same ?: tree as SLICE_LUTX (a bit-select with an X index would be
    // all-X, which is not the mux tree's Kleene behaviour)
    wire [31:0] s5 = A6 ? INIT[63:32] : INIT[31:0];
    wire [15:0] s4 = A5 ?   s5[31:16] :   s5[15:0];
    wire [ 7:0] s3 = A4 ?   s4[15:8]  :   s4[7:0];
    wire [ 3:0] s2 = A3 ?   s3[7:4]   :   s3[3:0];
    wire [ 1:0] s1 = A2 ?   s2[3:2]   :   s2[1:0];
    wire f = A1 ? s1[1] : s1[0];
    reg o = 1'bx;
    integer d = 124;
    always @(A1) d = TA1O6;
    always @(A2) d = TA2O6;
    always @(A3) d = TA3O6;
    always @(f) o <= #(d) f;
    assign O6 = o, O5 = 1'bx;
endmodule
