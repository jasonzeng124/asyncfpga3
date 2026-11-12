// tb_runt.v -- runt-pulse sweep through the research GLS's own primitives.
//
// Chain:  in -> LUT1 (identity on A1) -> [ICBUF D=`WIRE] -> LUT2 (identity) -> o2
// LUT1 output o1 is observed too.  Compile-time knobs (all optional):
//   `LUTMOD   module to use for the LUTs (default SLICE_LUTX, the GLS model;
//             LUT_TR = transport-delay LUT, LUT_RF = asymmetric rise/fall arc)
//   `TLUT     LUT path delay in ps (default 124, nextpnr's flat O6 arc)
//   `WIRE     ICBUF delay between the LUTs (default 0 = direct connection)
//   -DGLS_TRANSPORT_IC   ICBUF as the baked build has it (transport)
// For each input width w in [WMIN, WMAX] the bench emits one line
//   W <w> N1 <transitions on o1> W1 <o1 width> N2 <transitions on o2> W2 <o2 width>
// and for the two-pulse test (two w-wide pulses with gap g)
//   P <w> <g> N1 <n> N2 <n>
`timescale 1ps/1ps
`ifndef LUTMOD
 `define LUTMOD SLICE_LUTX
`endif
`ifndef TLUT
 `define TLUT 124
`endif
`ifndef WIRE
 `define WIRE 0
`endif
module tb_runt;
    reg in = 0;
    wire o1, m, o2;
    `LUTMOD #(.INIT(64'hAAAA_AAAA_AAAA_AAAA), .TA1O6(`TLUT))
        l1 (.A1(in), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O6(o1), .O5());
    generate if (`WIRE > 0) begin : gw
        ICBUF #(.D(`WIRE)) ic (.I(o1), .O(m));
    end else begin : gnw
        assign m = o1;
    end endgenerate
    `LUTMOD #(.INIT(64'hAAAA_AAAA_AAAA_AAAA), .TA1O6(`TLUT))
        l2 (.A1(m), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O6(o2), .O5());

    integer n1, n2; time r1, f1, r2, f2;
    always @(o1) if ($time > 5000) begin n1 = n1 + 1; if (o1 === 1'b1) r1 = $time; else f1 = $time; end
    always @(o2) if ($time > 5000) begin n2 = n2 + 1; if (o2 === 1'b1) r2 = $time; else f2 = $time; end

    integer w, g, wmin, wmax, gap;
    initial begin
        if (!$value$plusargs("WMIN=%d", wmin)) wmin = 1;
        if (!$value$plusargs("WMAX=%d", wmax)) wmax = 400;
        #10000;
        for (w = wmin; w <= wmax; w = w + 1) begin
            n1 = 0; n2 = 0; r1 = 0; f1 = 0; r2 = 0; f2 = 0;
            in = 1; #(w) in = 0;
            #(4 * `TLUT + 2 * `WIRE + 1000);
            $display("W %0d N1 %0d W1 %0d N2 %0d W2 %0d", w, n1, (n1 == 2) ? f1 - r1 : 0,
                     n2, (n2 == 2) ? f2 - r2 : 0);
        end
        // two pulses of width w separated by gap g
        for (w = 40; w <= 400; w = w + 40)
            for (g = 20; g <= 400; g = g + 20) begin
                n1 = 0; n2 = 0;
                in = 1; #(w) in = 0; #(g) in = 1; #(w) in = 0;
                #(4 * `TLUT + 2 * `WIRE + 1000);
                $display("P %0d %0d N1 %0d N2 %0d", w, g, n1, n2);
            end
        $finish;
    end
endmodule

// Transport-delay LUT: the zero-time mux tree of SLICE_LUTX followed by a
// pure (transport) delay -- the semantics of formal Core/Delay/Pure.lean with
// lo = hi.  NOT a GLS primitive: a reference to compare the GLS against.
module LUT_TR (input wire A1, A2, A3, A4, A5, A6, output wire O5, O6);
    parameter [63:0] INIT = 64'h0;
    parameter TA1O6 = 124;
    wire f = INIT[{A6, A5, A4, A3, A2, A1}];
    reg o = 1'bx;
    always @(f) o <= #(TA1O6) f;
    assign O6 = o, O5 = 1'bx;
endmodule

// Same mux tree with an asymmetric rise/fall module path, as prjxray's arcs
// are (O6 rise 56 / fall 124).  The research GLS emits one number for both
// edges; this asks what iverilog would do if the SDF carried two.
module LUT_RF (input wire A1, A2, A3, A4, A5, A6, output wire O5, O6);
    parameter [63:0] INIT = 64'h0;
    parameter TA1O6 = 124;
    parameter TRISE = 56;
    assign O6 = INIT[{A6, A5, A4, A3, A2, A1}];
    assign O5 = 1'bx;
    specify (A1 => O6) = (TRISE, TA1O6); endspecify
endmodule
