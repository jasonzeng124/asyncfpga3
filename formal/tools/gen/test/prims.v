// formal/tools/gen/test/prims.v -- NOT a library cell. Small modules whose
// synthesis is expected to use the non-LUT primitives (CARRY4, MUXF7, MUXF8,
// FDRE/FDSE/FDCE/FDPE, LDCE/LDPE), so that the interpreter's model of each
// primitive is checked against yosys's techmapping of a known function
// (Formal/Gen/ProofsPrims.lean). Nothing in cells/rtl/ uses these except FDRE
// (bd_flink).
`default_nettype none
module prims_add (input wire [3:0] a, input wire [3:0] b, input wire ci,
                  output wire [4:0] s);
    assign s = a + b + ci;
endmodule

// synth_xilinx does not infer MUXF7/MUXF8 by default (-widemux 0), so they
// are instantiated, as a cell author would.
module prims_mux8 (input wire [7:0] d, input wire [2:0] sel, output wire z);
    wire lo = d[{1'b0, sel[1:0]}];
    wire hi = d[{1'b1, sel[1:0]}];
    MUXF7 m (.I0(lo), .I1(hi), .S(sel[2]), .O(z));
endmodule

module prims_muxf8 (input wire [3:0] d, input wire [1:0] sel, output wire z);
    wire [3:0] l;
    wire m0, m1;
    genvar i;
    generate for (i = 0; i < 4; i = i + 1) begin : b
        (* keep *) LUT1 #(.INIT(2'h2)) u (.I0(d[i]), .O(l[i]));
    end endgenerate
    MUXF7 u0 (.I0(l[0]), .I1(l[1]), .S(sel[0]), .O(m0));
    MUXF7 u1 (.I0(l[2]), .I1(l[3]), .S(sel[0]), .O(m1));
    MUXF8 u2 (.I0(m0), .I1(m1), .S(sel[1]), .O(z));
endmodule

module prims_ff (input wire c, input wire ce, input wire r, input wire d,
                 output reg qr, output reg qs, output reg qc, output reg qp);
    always @(posedge c) if (r) qr <= 1'b0; else if (ce) qr <= d;
    always @(posedge c) if (r) qs <= 1'b1; else if (ce) qs <= d;
    always @(posedge c or posedge r) if (r) qc <= 1'b0; else if (ce) qc <= d;
    always @(posedge c or posedge r) if (r) qp <= 1'b1; else if (ce) qp <= d;
endmodule

module prims_lat (input wire g, input wire r, input wire d,
                  output reg qc, output reg qp);
    always @* if (r) qc = 1'b0; else if (g) qc = d;
    always @* if (r) qp = 1'b1; else if (g) qp = d;
endmodule
`default_nettype wire
