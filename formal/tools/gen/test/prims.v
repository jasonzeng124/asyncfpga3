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

module prims_mux8 (input wire [7:0] d, input wire [2:0] sel, output wire z);
    assign z = d[sel];
endmodule

module prims_mux16 (input wire [15:0] d, input wire [3:0] sel, output wire z);
    assign z = d[sel];
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
