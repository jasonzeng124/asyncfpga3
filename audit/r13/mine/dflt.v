// auditor r13: hand DSP48E1 relying on the Xilinx/yosys DEFAULT AREG=1 ACASCREG=1
// BREG=1 BCASCREG=1 (parameters omitted); every other register set explicitly.
module dflt(input clk, input din, output dout);
    reg [63:0] sr = 64'h0;
    always @(posedge clk) sr <= {sr[62:0], din ^ sr[63] ^ sr[60]};
    wire [24:0] la; wire [17:0] lb;
    genvar i;
    generate for (i = 0; i < 25; i = i + 1) begin : ga
        (* keep *) LUT2 #(.INIT(4'h6)) u (.O(la[i]), .I0(sr[i]), .I1(sr[i+30])); end
    for (i = 0; i < 18; i = i + 1) begin : gb
        (* keep *) LUT2 #(.INIT(4'h9)) u (.O(lb[i]), .I0(sr[i+3]), .I1(sr[i+40])); end endgenerate
    wire [47:0] p1;
    DSP48E1 #(.CREG(0),.MREG(0),.PREG(0),.ADREG(0),.DREG(0),
              .INMODEREG(0),.OPMODEREG(0),.ALUMODEREG(0),.CARRYINREG(0),.CARRYINSELREG(0),.USE_DPORT("FALSE"),
              .A_INPUT("DIRECT"),.B_INPUT("DIRECT"),.USE_SIMD("ONE48"),.USE_MULT("MULTIPLY"))
      u1 (.CLK(clk),.A({5'd0, la}),.B(lb),.C(48'd0),.D(25'd0),.PCIN(48'd0),.ACIN(30'd0),.BCIN(18'd0),
          .CARRYCASCIN(1'b0),.MULTSIGNIN(1'b0),.OPMODE(7'b0000101),.ALUMODE(4'd0),.INMODE(5'd0),.CARRYINSEL(3'd0),
          .CARRYIN(1'b0),.CEA1(1'b0),.CEA2(1'b1),.CEB1(1'b0),.CEB2(1'b1),.CEC(1'b0),.CEM(1'b0),.CEP(1'b0),.CEAD(1'b0),
          .CED(1'b0),.CEINMODE(1'b0),.CECTRL(1'b0),.CEALUMODE(1'b0),.CECARRYIN(1'b0),.RSTA(1'b0),.RSTB(1'b0),
          .RSTC(1'b0),.RSTM(1'b0),.RSTP(1'b0),.RSTD(1'b0),.RSTINMODE(1'b0),.RSTCTRL(1'b0),.RSTALUMODE(1'b0),
          .RSTALLCARRYIN(1'b0),.P(p1));
    reg [47:0] q; always @(posedge clk) q <= p1;
    assign dout = ^q;
endmodule
