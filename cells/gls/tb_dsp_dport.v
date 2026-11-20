// tb_dsp_dport.v -- hand check of prims.v's DSP48E1_DSP48E1 S8 configurations
// (cells/gls/dsp_model.py): the pre-adder with D (DPORT=1: USE_DPORT=TRUE,
// INMODE=00100), the B cascade (BCASC=1: B_INPUT=CASCADE) and BCOUT, against
// expectations written here from the UG479 / yosys cells_sim.v equations,
// not from the model's code:
//
//   head (share_test_2's DSP48_X0Y26): every register off, A and B direct,
//     OPMODE 0000101 (Z = 0):     M = sext(A[24:0]) * sext(B);  P = PCOUT = M
//                                 BCOUT = B  (BREG = BCASCREG = 0)
//   tail (DSP48_X0Y27): USE_DPORT=TRUE INMODE=00100, B_INPUT=CASCADE,
//     OPMODE 1010101 (Z = PCIN>>>17):
//                                 AD = (D + A[24:0]) mod 2^25, signed
//                                 P  = (PCIN >>> 17) + sext(AD * BCIN)
//   chained as the route has them: head BCOUT -> tail BCIN, head PCOUT -> PCIN.
//
// With -DYOSYS_REF the same two cells as yosys's own DSP48E1 (techlibs/xilinx/
// cells_sim.v; only that module: the file's BUFGCTRL and CARRY4 clash with
// prims.v's) run beside them and must agree bit for bit.
// -DGLS_DSP_PREADD_FAULT=1 (the pre-adder subtracts) or =2 (D dropped) must
// FAIL: the negative control.
//
//   iverilog -gspecify -o tb_dsp_dport.vvp cells/gls/tb_dsp_dport.v cells/gls/prims.v && vvp tb_dsp_dport.vvp
//   awk '/^module DSP48E1 \(/,/^endmodule/' $TC/openxc7/share/yosys/xilinx/cells_sim.v > dsp48e1_yosys.v
//   iverilog -g2012 -gspecify -DYOSYS_REF -o tb_dsp_dport_y.vvp cells/gls/tb_dsp_dport.v cells/gls/prims.v \
//       dsp48e1_yosys.v && vvp tb_dsp_dport_y.vvp
//
// Prints DSPDPORT PASS / DSPDPORT FAIL n at the end.
`timescale 1ps/1ps
module dsp_dport_pair (input [29:0] a0, input [17:0] b0, input [29:0] a1, input [24:0] d1,
                       output [47:0] p0, output [47:0] pcout0, output [17:0] bcout0, output [47:0] p1);
  wire [47:0] pc;
  wire [17:0] bc;
  wire [47:0] pcout1;
  DSP48E1_DSP48E1 #(.ZMUX(0), .ACASC(0)) u0 (
    .A0(a0[0]), .A1(a0[1]), .A2(a0[2]), .A3(a0[3]), .A4(a0[4]), .A5(a0[5]), .A6(a0[6]), .A7(a0[7]), .A8(a0[8]), .A9(a0[9]), .A10(a0[10]), .A11(a0[11]), .A12(a0[12]), .A13(a0[13]), .A14(a0[14]), .A15(a0[15]), .A16(a0[16]), .A17(a0[17]), .A18(a0[18]), .A19(a0[19]), .A20(a0[20]), .A21(a0[21]), .A22(a0[22]), .A23(a0[23]), .A24(a0[24]), .A25(a0[25]), .A26(a0[26]), .A27(a0[27]), .A28(a0[28]), .A29(a0[29]),
    .B0(b0[0]), .B1(b0[1]), .B2(b0[2]), .B3(b0[3]), .B4(b0[4]), .B5(b0[5]), .B6(b0[6]), .B7(b0[7]), .B8(b0[8]), .B9(b0[9]), .B10(b0[10]), .B11(b0[11]), .B12(b0[12]), .B13(b0[13]), .B14(b0[14]), .B15(b0[15]), .B16(b0[16]), .B17(b0[17]),
    .P0(p0[0]), .P1(p0[1]), .P2(p0[2]), .P3(p0[3]), .P4(p0[4]), .P5(p0[5]), .P6(p0[6]), .P7(p0[7]), .P8(p0[8]), .P9(p0[9]), .P10(p0[10]), .P11(p0[11]), .P12(p0[12]), .P13(p0[13]), .P14(p0[14]), .P15(p0[15]), .P16(p0[16]), .P17(p0[17]), .P18(p0[18]), .P19(p0[19]), .P20(p0[20]), .P21(p0[21]), .P22(p0[22]), .P23(p0[23]), .P24(p0[24]), .P25(p0[25]), .P26(p0[26]), .P27(p0[27]), .P28(p0[28]), .P29(p0[29]), .P30(p0[30]), .P31(p0[31]), .P32(p0[32]), .P33(p0[33]), .P34(p0[34]), .P35(p0[35]), .P36(p0[36]), .P37(p0[37]), .P38(p0[38]), .P39(p0[39]), .P40(p0[40]), .P41(p0[41]), .P42(p0[42]), .P43(p0[43]), .P44(p0[44]), .P45(p0[45]), .P46(p0[46]), .P47(p0[47]),
    .PCOUT0(pc[0]), .PCOUT1(pc[1]), .PCOUT2(pc[2]), .PCOUT3(pc[3]), .PCOUT4(pc[4]), .PCOUT5(pc[5]), .PCOUT6(pc[6]), .PCOUT7(pc[7]), .PCOUT8(pc[8]), .PCOUT9(pc[9]), .PCOUT10(pc[10]), .PCOUT11(pc[11]), .PCOUT12(pc[12]), .PCOUT13(pc[13]), .PCOUT14(pc[14]), .PCOUT15(pc[15]), .PCOUT16(pc[16]), .PCOUT17(pc[17]), .PCOUT18(pc[18]), .PCOUT19(pc[19]), .PCOUT20(pc[20]), .PCOUT21(pc[21]), .PCOUT22(pc[22]), .PCOUT23(pc[23]), .PCOUT24(pc[24]), .PCOUT25(pc[25]), .PCOUT26(pc[26]), .PCOUT27(pc[27]), .PCOUT28(pc[28]), .PCOUT29(pc[29]), .PCOUT30(pc[30]), .PCOUT31(pc[31]), .PCOUT32(pc[32]), .PCOUT33(pc[33]), .PCOUT34(pc[34]), .PCOUT35(pc[35]), .PCOUT36(pc[36]), .PCOUT37(pc[37]), .PCOUT38(pc[38]), .PCOUT39(pc[39]), .PCOUT40(pc[40]), .PCOUT41(pc[41]), .PCOUT42(pc[42]), .PCOUT43(pc[43]), .PCOUT44(pc[44]), .PCOUT45(pc[45]), .PCOUT46(pc[46]), .PCOUT47(pc[47]),
    .BCOUT0(bc[0]), .BCOUT1(bc[1]), .BCOUT2(bc[2]), .BCOUT3(bc[3]), .BCOUT4(bc[4]), .BCOUT5(bc[5]), .BCOUT6(bc[6]), .BCOUT7(bc[7]), .BCOUT8(bc[8]), .BCOUT9(bc[9]), .BCOUT10(bc[10]), .BCOUT11(bc[11]), .BCOUT12(bc[12]), .BCOUT13(bc[13]), .BCOUT14(bc[14]), .BCOUT15(bc[15]), .BCOUT16(bc[16]), .BCOUT17(bc[17]));
  DSP48E1_DSP48E1 #(.ZMUX(5), .ACASC(0), .XMUX(1), .YMUX(1), .ALUMODE(0), .AGATE(0), .CIN(0), .MUNK(0),
                    .DPORT(1), .BCASC(1)) u1 (
    .A0(a1[0]), .A1(a1[1]), .A2(a1[2]), .A3(a1[3]), .A4(a1[4]), .A5(a1[5]), .A6(a1[6]), .A7(a1[7]), .A8(a1[8]), .A9(a1[9]), .A10(a1[10]), .A11(a1[11]), .A12(a1[12]), .A13(a1[13]), .A14(a1[14]), .A15(a1[15]), .A16(a1[16]), .A17(a1[17]), .A18(a1[18]), .A19(a1[19]), .A20(a1[20]), .A21(a1[21]), .A22(a1[22]), .A23(a1[23]), .A24(a1[24]), .A25(a1[25]), .A26(a1[26]), .A27(a1[27]), .A28(a1[28]), .A29(a1[29]),
    .D0(d1[0]), .D1(d1[1]), .D2(d1[2]), .D3(d1[3]), .D4(d1[4]), .D5(d1[5]), .D6(d1[6]), .D7(d1[7]), .D8(d1[8]), .D9(d1[9]), .D10(d1[10]), .D11(d1[11]), .D12(d1[12]), .D13(d1[13]), .D14(d1[14]), .D15(d1[15]), .D16(d1[16]), .D17(d1[17]), .D18(d1[18]), .D19(d1[19]), .D20(d1[20]), .D21(d1[21]), .D22(d1[22]), .D23(d1[23]), .D24(d1[24]),
    .BCIN0(bc[0]), .BCIN1(bc[1]), .BCIN2(bc[2]), .BCIN3(bc[3]), .BCIN4(bc[4]), .BCIN5(bc[5]), .BCIN6(bc[6]), .BCIN7(bc[7]), .BCIN8(bc[8]), .BCIN9(bc[9]), .BCIN10(bc[10]), .BCIN11(bc[11]), .BCIN12(bc[12]), .BCIN13(bc[13]), .BCIN14(bc[14]), .BCIN15(bc[15]), .BCIN16(bc[16]), .BCIN17(bc[17]),
    .PCIN0(pc[0]), .PCIN1(pc[1]), .PCIN2(pc[2]), .PCIN3(pc[3]), .PCIN4(pc[4]), .PCIN5(pc[5]), .PCIN6(pc[6]), .PCIN7(pc[7]), .PCIN8(pc[8]), .PCIN9(pc[9]), .PCIN10(pc[10]), .PCIN11(pc[11]), .PCIN12(pc[12]), .PCIN13(pc[13]), .PCIN14(pc[14]), .PCIN15(pc[15]), .PCIN16(pc[16]), .PCIN17(pc[17]), .PCIN18(pc[18]), .PCIN19(pc[19]), .PCIN20(pc[20]), .PCIN21(pc[21]), .PCIN22(pc[22]), .PCIN23(pc[23]), .PCIN24(pc[24]), .PCIN25(pc[25]), .PCIN26(pc[26]), .PCIN27(pc[27]), .PCIN28(pc[28]), .PCIN29(pc[29]), .PCIN30(pc[30]), .PCIN31(pc[31]), .PCIN32(pc[32]), .PCIN33(pc[33]), .PCIN34(pc[34]), .PCIN35(pc[35]), .PCIN36(pc[36]), .PCIN37(pc[37]), .PCIN38(pc[38]), .PCIN39(pc[39]), .PCIN40(pc[40]), .PCIN41(pc[41]), .PCIN42(pc[42]), .PCIN43(pc[43]), .PCIN44(pc[44]), .PCIN45(pc[45]), .PCIN46(pc[46]), .PCIN47(pc[47]),
    .P0(p1[0]), .P1(p1[1]), .P2(p1[2]), .P3(p1[3]), .P4(p1[4]), .P5(p1[5]), .P6(p1[6]), .P7(p1[7]), .P8(p1[8]), .P9(p1[9]), .P10(p1[10]), .P11(p1[11]), .P12(p1[12]), .P13(p1[13]), .P14(p1[14]), .P15(p1[15]), .P16(p1[16]), .P17(p1[17]), .P18(p1[18]), .P19(p1[19]), .P20(p1[20]), .P21(p1[21]), .P22(p1[22]), .P23(p1[23]), .P24(p1[24]), .P25(p1[25]), .P26(p1[26]), .P27(p1[27]), .P28(p1[28]), .P29(p1[29]), .P30(p1[30]), .P31(p1[31]), .P32(p1[32]), .P33(p1[33]), .P34(p1[34]), .P35(p1[35]), .P36(p1[36]), .P37(p1[37]), .P38(p1[38]), .P39(p1[39]), .P40(p1[40]), .P41(p1[41]), .P42(p1[42]), .P43(p1[43]), .P44(p1[44]), .P45(p1[45]), .P46(p1[46]), .P47(p1[47]),
    .PCOUT0(pcout1[0]), .PCOUT1(pcout1[1]), .PCOUT2(pcout1[2]), .PCOUT3(pcout1[3]), .PCOUT4(pcout1[4]), .PCOUT5(pcout1[5]), .PCOUT6(pcout1[6]), .PCOUT7(pcout1[7]), .PCOUT8(pcout1[8]), .PCOUT9(pcout1[9]), .PCOUT10(pcout1[10]), .PCOUT11(pcout1[11]), .PCOUT12(pcout1[12]), .PCOUT13(pcout1[13]), .PCOUT14(pcout1[14]), .PCOUT15(pcout1[15]), .PCOUT16(pcout1[16]), .PCOUT17(pcout1[17]), .PCOUT18(pcout1[18]), .PCOUT19(pcout1[19]), .PCOUT20(pcout1[20]), .PCOUT21(pcout1[21]), .PCOUT22(pcout1[22]), .PCOUT23(pcout1[23]), .PCOUT24(pcout1[24]), .PCOUT25(pcout1[25]), .PCOUT26(pcout1[26]), .PCOUT27(pcout1[27]), .PCOUT28(pcout1[28]), .PCOUT29(pcout1[29]), .PCOUT30(pcout1[30]), .PCOUT31(pcout1[31]), .PCOUT32(pcout1[32]), .PCOUT33(pcout1[33]), .PCOUT34(pcout1[34]), .PCOUT35(pcout1[35]), .PCOUT36(pcout1[36]), .PCOUT37(pcout1[37]), .PCOUT38(pcout1[38]), .PCOUT39(pcout1[39]), .PCOUT40(pcout1[40]), .PCOUT41(pcout1[41]), .PCOUT42(pcout1[42]), .PCOUT43(pcout1[43]), .PCOUT44(pcout1[44]), .PCOUT45(pcout1[45]), .PCOUT46(pcout1[46]), .PCOUT47(pcout1[47]));
  assign pcout0 = pc;
  assign bcout0 = bc;
endmodule

`ifdef YOSYS_REF
module dsp_dport_yref (input [29:0] a0, input [17:0] b0, input [29:0] a1, input [24:0] d1,
                       output [47:0] p0, output [47:0] pcout0, output [17:0] bcout0, output [47:0] p1);
  wire [47:0] pc;
  wire [17:0] bc;
  DSP48E1 #(.AREG(0), .ACASCREG(0), .BREG(0), .BCASCREG(0), .CREG(0), .DREG(0), .ADREG(0), .MREG(0), .PREG(0),
            .INMODEREG(0), .OPMODEREG(0), .ALUMODEREG(0), .CARRYINREG(0), .CARRYINSELREG(0),
            .USE_DPORT("FALSE"), .A_INPUT("DIRECT"), .B_INPUT("DIRECT")) y0 (
    .A(a0), .B(b0), .C(48'd0), .D(25'd0), .ACIN(30'd0), .BCIN(18'd0), .PCIN(48'd0), .INMODE(5'b00000),
    .OPMODE(7'b0000101), .ALUMODE(4'd0), .CARRYINSEL(3'd0), .CARRYIN(1'b0), .CLK(1'b0),
    .P(p0), .PCOUT(pc), .BCOUT(bc));
  DSP48E1 #(.AREG(0), .ACASCREG(0), .BREG(0), .BCASCREG(0), .CREG(0), .DREG(0), .ADREG(0), .MREG(0), .PREG(0),
            .INMODEREG(0), .OPMODEREG(0), .ALUMODEREG(0), .CARRYINREG(0), .CARRYINSELREG(0),
            .USE_DPORT("TRUE"), .A_INPUT("DIRECT"), .B_INPUT("CASCADE")) y1 (
    .A(a1), .B(18'd0), .C(48'd0), .D(d1), .ACIN(30'd0), .BCIN(bc), .PCIN(pc), .INMODE(5'b00100),
    .OPMODE(7'b1010101), .ALUMODE(4'd0), .CARRYINSEL(3'd0), .CARRYIN(1'b0), .CLK(1'b0),
    .P(p1));
  assign pcout0 = pc;
  assign bcout0 = bc;
endmodule
`endif

module tb;
  reg [29:0] a0, a1;
  reg [17:0] b0;
  reg [24:0] d1;
  wire [47:0] p0, pcout0, p1;
  wire [17:0] bcout0;
  dsp_dport_pair dut (.a0(a0), .b0(b0), .a1(a1), .d1(d1), .p0(p0), .pcout0(pcout0), .bcout0(bcout0), .p1(p1));
`ifdef YOSYS_REF
  wire [47:0] yp0, ypcout0, yp1;
  wire [17:0] ybcout0;
  dsp_dport_yref yref (.a0(a0), .b0(b0), .a1(a1), .d1(d1), .p0(yp0), .pcout0(ypcout0), .bcout0(ybcout0), .p1(yp1));
`endif
  // the expectation, from the equations in the header
  reg signed [24:0] ea0, ead;
  reg signed [17:0] eb;
  reg signed [42:0] em0, em1;
  reg [47:0] ep0, ep1;
  integer n = 0, bad = 0, ybad = 0, wraps = 0, k;
  task check;
    begin
      ea0 = a0[24:0];
      eb = b0;
      em0 = ea0 * eb;
      ep0 = {{5{em0[42]}}, em0};
      ead = d1 + a1[24:0];
      if ({1'b0, d1} + {1'b0, a1[24:0]} > 26'h1ffffff) wraps = wraps + 1;
      em1 = ead * eb;
      ep1 = {{17{ep0[47]}}, ep0[47:17]} + {{5{em1[42]}}, em1};
      #20000;
      n = n + 1;
      if (p0 !== ep0 || pcout0 !== ep0 || bcout0 !== b0 || p1 !== ep1) begin
        bad = bad + 1;
        if (bad <= 5)
          $display("MISMATCH a0=%h b0=%h a1=%h d1=%h: p0 %h (exp %h) bcout0 %h p1 %h (exp %h)",
                   a0, b0, a1, d1, p0, ep0, bcout0, p1, ep1);
      end
`ifdef YOSYS_REF
      if (yp0 !== p0 || ypcout0 !== pcout0 || ybcout0 !== bcout0 || yp1 !== p1) begin
        ybad = ybad + 1;
        if (ybad <= 5)
          $display("YOSYS DIFFERS a0=%h b0=%h a1=%h d1=%h: prims p1 %h yosys p1 %h", a0, b0, a1, d1, p1, yp1);
      end
`endif
    end
  endtask
  initial begin
    // edges: the pre-adder's 25-bit wrap both ways, operand extremes, zeros
    a0 = 30'h0; b0 = 18'h0; a1 = 30'h0; d1 = 25'h0; check;
    a0 = 30'h1; b0 = 18'h1; a1 = 30'h1; d1 = 25'h1ffffff; check;          // D + A = 2^25 -> 0
    a0 = 30'h0ffffff; b0 = 18'h1ffff; a1 = 30'h1; d1 = 25'h0ffffff; check; // +max + 1 -> -2^24
    a0 = 30'h1000000; b0 = 18'h20000; a1 = 30'h1000000; d1 = 25'h1000000; check;  // -2^24 + -2^24 -> 0
    a0 = 30'h3fffffff; b0 = 18'h3ffff; a1 = 30'h3fffffff; d1 = 25'h1ffffff; check; // -1 + -1, A[29:25] ignored
    a0 = 30'h2aaaaaaa; b0 = 18'h15555; a1 = 30'h15555555; d1 = 25'h0aaaaaa; check;
    a0 = 30'h0001fff; b0 = 18'h06f85; a1 = 30'h00007ff; d1 = 25'h1fff800; check; // share_test_2's B, an 11-bit slice
    for (k = 0; k < 3000; k = k + 1) begin
      a0 = $random; b0 = $random; a1 = $random; d1 = $random;
      if (k % 5 == 0) b0 = 18'h06f85;          // the constant the route cascades (0x6f85)
      if (k % 7 == 0) d1 = -a1[24:0] + (k % 3); // around the pre-adder's zero
      check;
    end
`ifdef YOSYS_REF
    $display("DSPDPORT yosys DSP48E1 reference: %0d of %0d vectors differ", ybad, n);
`endif
    if (bad == 0 && ybad == 0) $display("DSPDPORT PASS  (%0d vectors, %0d with the pre-adder wrapping, 0 mismatches)", n, wraps);
    else $display("DSPDPORT FAIL %0d  (%0d vectors, %0d yosys differences)", bad, n, ybad);
    $finish;
  end
endmodule
