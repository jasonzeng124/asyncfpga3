// The bitstream seam's probe: every encoding the three FASM-writer bugs in
// patches/ got wrong, in one design small enough to route in seconds.
//
//   LUT6s with one net on two inputs: the packer puts both logical inputs on
//   one physical pin and writes X_ORIG_PORT_A<n> run together ('I2I0 '),
//   which is what nextpnr-xilinx-lut-pinmap.patch is about.
//   Three DSP48E1s: operands straight from LUTs (AREG=0), through one
//   register (AREG=1, ACASCREG=1 -- the case nextpnr-xilinx-dsp-areg.patch
//   is about) and through two (AREG=2, ACASCREG=2).  Every one has INMODE,
//   ALUMODE2/3 and OPMODE6 tied off, which nextpnr-xilinx-dsp-constpins.patch
//   is about.
//
// Only the encoding is checked (verify/fasm_audit.py); nothing here is run.
module fasm_probe(input clk, input din, output dout);
    reg [63:0] sr = 64'h0;
    always @(posedge clk) sr <= {sr[62:0], din ^ sr[63]};
    wire [31:0] l;
    genvar i;
    generate for (i = 0; i < 32; i = i + 1) begin : g
        (* keep *) LUT6 #(.INIT(64'h6996_9669_A5C3_3C5A ^ (64'h1 << i))) u (
            .O(l[i]), .I0(sr[i]), .I1(sr[i+1]), .I2(sr[i]), .I3(sr[i+2]),
            .I4(sr[(i+7)%64]), .I5(sr[i+1]));
    end endgenerate
    // AREG=0: operands are LUT outputs, nothing to absorb.
    reg [31:0] q0;
    always @(posedge clk) q0 <= l[15:0] * l[31:16];
    // AREG=1: one register, of LUT outputs.
    reg [15:0] xa, xb; reg [31:0] q1;
    always @(posedge clk) begin xa <= l[15:0] ^ sr[15:0]; xb <= l[31:16] ^ sr[31:16]; end
    always @(posedge clk) q1 <= xa * xb;
    // AREG=2: two registers (sr itself and ra).
    reg [15:0] ra, rb; reg [31:0] q2;
    always @(posedge clk) begin ra <= sr[15:0]; rb <= sr[47:32]; end
    always @(posedge clk) q2 <= ra * rb;
    assign dout = ^l ^ ^q0 ^ ^q1 ^ ^q2;
endmodule
