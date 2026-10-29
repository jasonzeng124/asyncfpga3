// auditor r13: own dsp_areg good/buggy pair.
//  u1: hand DSP48E1 AREG=1/ACASCREG=1 with CEA1=CEA2=1 (A1 register live),
//      PREG=1 -> under research's decode of the unpatched bits (AREG=2) the
//      A path gets ONE EXTRA stage (not "never loads").
//  u2: hand DSP48E1 BREG=1/BCASCREG=1 only (AREG=0), CEB1=0 CEB2=1, MREG=1.
//  u3: inferred multiply whose operand registers have a LIVE enable (en).
module mine(input clk, input din, output dout);
    reg [63:0] sr = 64'h0;
    always @(posedge clk) sr <= {sr[62:0], din ^ sr[63] ^ sr[60]};
    wire [47:0] p1, p2;
    DSP48E1 #(.AREG(1),.ACASCREG(1),.BREG(0),.BCASCREG(0),.CREG(0),.MREG(0),.PREG(1),.ADREG(0),.DREG(0),
              .INMODEREG(0),.OPMODEREG(0),.ALUMODEREG(0),.CARRYINREG(0),.CARRYINSELREG(0),.USE_DPORT("FALSE"),.A_INPUT("DIRECT"),.B_INPUT("DIRECT"),.USE_SIMD("ONE48"),.USE_MULT("MULTIPLY"))
      u1 (.CLK(clk),.A({5'd0, sr[24:0]}),.B(sr[42:25]),.C(48'd0),.D(25'd0),.PCIN(48'd0),.ACIN(30'd0),.BCIN(18'd0),
          .CARRYCASCIN(1'b0),.MULTSIGNIN(1'b0),.OPMODE(7'b0000101),.ALUMODE(4'd0),.INMODE(5'd0),.CARRYINSEL(3'd0),
          .CARRYIN(1'b0),.CEA1(1'b1),.CEA2(1'b1),.CEB1(1'b0),.CEB2(1'b0),.CEC(1'b0),.CEM(1'b0),.CEP(1'b1),.CEAD(1'b0),
          .CED(1'b0),.CEINMODE(1'b0),.CECTRL(1'b0),.CEALUMODE(1'b0),.CECARRYIN(1'b0),.RSTA(1'b0),.RSTB(1'b0),
          .RSTC(1'b0),.RSTM(1'b0),.RSTP(1'b0),.RSTD(1'b0),.RSTINMODE(1'b0),.RSTCTRL(1'b0),.RSTALUMODE(1'b0),
          .RSTALLCARRYIN(1'b0),.P(p1));
    DSP48E1 #(.AREG(0),.ACASCREG(0),.BREG(1),.BCASCREG(1),.CREG(0),.MREG(1),.PREG(0),.ADREG(0),.DREG(0),
              .INMODEREG(0),.OPMODEREG(0),.ALUMODEREG(0),.CARRYINREG(0),.CARRYINSELREG(0),.USE_DPORT("FALSE"),.A_INPUT("DIRECT"),.B_INPUT("DIRECT"),.USE_SIMD("ONE48"),.USE_MULT("MULTIPLY"))
      u2 (.CLK(clk),.A({5'd0, sr[63:39]}),.B(sr[17:0]),.C(48'd0),.D(25'd0),.PCIN(48'd0),.ACIN(30'd0),.BCIN(18'd0),
          .CARRYCASCIN(1'b0),.MULTSIGNIN(1'b0),.OPMODE(7'b0000101),.ALUMODE(4'd0),.INMODE(5'd0),.CARRYINSEL(3'd0),
          .CARRYIN(1'b0),.CEA1(1'b0),.CEA2(1'b0),.CEB1(1'b0),.CEB2(1'b1),.CEC(1'b0),.CEM(1'b1),.CEP(1'b0),.CEAD(1'b0),
          .CED(1'b0),.CEINMODE(1'b0),.CECTRL(1'b0),.CEALUMODE(1'b0),.CECARRYIN(1'b0),.RSTA(1'b0),.RSTB(1'b0),
          .RSTC(1'b0),.RSTM(1'b0),.RSTP(1'b0),.RSTD(1'b0),.RSTINMODE(1'b0),.RSTCTRL(1'b0),.RSTALUMODE(1'b0),
          .RSTALLCARRYIN(1'b0),.P(p2));
    wire en = sr[5] ^ sr[9];
    reg [15:0] ea, eb; reg [31:0] q3;
    always @(posedge clk) if (en) begin ea <= sr[15:0] ^ sr[31:16]; eb <= sr[47:32] ^ sr[63:48]; end
    always @(posedge clk) q3 <= ea * eb;
    assign dout = ^p1 ^ ^p2 ^ ^q3;
endmodule
