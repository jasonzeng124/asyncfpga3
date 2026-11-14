// tb_dsp_reg.v -- hand check of prims.v's REGISTERED DSP48E1_DSP48E1 (S7)
// against expectations written from UG479's register description, not from
// the model's code:
//
//   * latency: with LA registers on the A path (AREG, or 1 with INMODE[0]=A1
//     and AREG=2, plus MREG, plus PREG) the P sampled just before rising edge
//     e+1 is f(A as it was at edge e+1-LA).  Same for B and C.  (LA=0: the
//     inputs present now.)
//   * CE: a register loads only at an edge where its CE is 1, else it holds;
//     A2 with AREG=2 loads the value A1 held BEFORE that edge.
//   * RST: synchronous, over CE: the register is 0 after an edge with RST=1.
//   * ACOUT: A1 when AREG=2 and ACASCREG=1, else A2 (UG479 Table 2-1).
//   * IS_CLK_INVERTED (CLKINV=1): registers load on the falling edge.
//   * PREG with Z=P (OPMODE 010_01_01): P accumulates M every enabled edge.
//
//   iverilog -gspecify -o tb_dsp_reg.vvp cells/gls/tb_dsp_reg.v cells/gls/prims.v && vvp tb_dsp_reg.vvp
//
// Prints one line per check and DSPREG PASS / DSPREG FAIL n at the end.
`timescale 1ps/1ps
module dut_wrap #(parameter AREG=0, ACASCREG=0, BREG=0, BCASCREG=0, CREG=0, MREG=0, PREG=0,
                  ASEL1=0, BSEL1=0, CLKINV=0, XMUX=1, YMUX=1, ZMUX=0)
  (input clk, input [29:0] a, input [17:0] b, input [47:0] c,
   input cea1, cea2, ceb1, ceb2, cec, cem, cep, rsta, rstb, rstc, rstm, rstp,
   output [47:0] p, output [29:0] acout);
  DSP48E1_DSP48E1 #(.ZMUX(ZMUX), .ACASC(0), .XMUX(XMUX), .YMUX(YMUX), .ALUMODE(0), .AGATE(0), .CIN(0), .MUNK(0),
                    .AREG(AREG), .ACASCREG(ACASCREG), .BREG(BREG), .BCASCREG(BCASCREG), .CREG(CREG),
                    .MREG(MREG), .PREG(PREG), .ASEL1(ASEL1), .BSEL1(BSEL1), .CLKINV(CLKINV)) u (
    .A0(a[0]), .A1(a[1]), .A2(a[2]), .A3(a[3]), .A4(a[4]), .A5(a[5]), .A6(a[6]), .A7(a[7]), .A8(a[8]), .A9(a[9]),
    .A10(a[10]), .A11(a[11]), .A12(a[12]), .A13(a[13]), .A14(a[14]), .A15(a[15]), .A16(a[16]), .A17(a[17]), .A18(a[18]), .A19(a[19]),
    .A20(a[20]), .A21(a[21]), .A22(a[22]), .A23(a[23]), .A24(a[24]), .A25(a[25]), .A26(a[26]), .A27(a[27]), .A28(a[28]), .A29(a[29]),
    .B0(b[0]), .B1(b[1]), .B2(b[2]), .B3(b[3]), .B4(b[4]), .B5(b[5]), .B6(b[6]), .B7(b[7]), .B8(b[8]), .B9(b[9]),
    .B10(b[10]), .B11(b[11]), .B12(b[12]), .B13(b[13]), .B14(b[14]), .B15(b[15]), .B16(b[16]), .B17(b[17]),
    .C0(c[0]), .C1(c[1]), .C2(c[2]), .C3(c[3]), .C4(c[4]), .C5(c[5]), .C6(c[6]), .C7(c[7]), .C8(c[8]), .C9(c[9]),
    .C10(c[10]), .C11(c[11]), .C12(c[12]), .C13(c[13]), .C14(c[14]), .C15(c[15]), .C16(c[16]), .C17(c[17]), .C18(c[18]), .C19(c[19]),
    .C20(c[20]), .C21(c[21]), .C22(c[22]), .C23(c[23]), .C24(c[24]), .C25(c[25]), .C26(c[26]), .C27(c[27]), .C28(c[28]), .C29(c[29]),
    .C30(c[30]), .C31(c[31]), .C32(c[32]), .C33(c[33]), .C34(c[34]), .C35(c[35]), .C36(c[36]), .C37(c[37]), .C38(c[38]), .C39(c[39]),
    .C40(c[40]), .C41(c[41]), .C42(c[42]), .C43(c[43]), .C44(c[44]), .C45(c[45]), .C46(c[46]), .C47(c[47]),
    .CLK(clk), .CEA1(cea1), .CEA2(cea2), .CEB1(ceb1), .CEB2(ceb2), .CEC(cec), .CEM(cem), .CEP(cep),
    .RSTA(rsta), .RSTB(rstb), .RSTC(rstc), .RSTM(rstm), .RSTP(rstp),
    .P0(p[0]), .P1(p[1]), .P2(p[2]), .P3(p[3]), .P4(p[4]), .P5(p[5]), .P6(p[6]), .P7(p[7]), .P8(p[8]), .P9(p[9]),
    .P10(p[10]), .P11(p[11]), .P12(p[12]), .P13(p[13]), .P14(p[14]), .P15(p[15]), .P16(p[16]), .P17(p[17]), .P18(p[18]), .P19(p[19]),
    .P20(p[20]), .P21(p[21]), .P22(p[22]), .P23(p[23]), .P24(p[24]), .P25(p[25]), .P26(p[26]), .P27(p[27]), .P28(p[28]), .P29(p[29]),
    .P30(p[30]), .P31(p[31]), .P32(p[32]), .P33(p[33]), .P34(p[34]), .P35(p[35]), .P36(p[36]), .P37(p[37]), .P38(p[38]), .P39(p[39]),
    .P40(p[40]), .P41(p[41]), .P42(p[42]), .P43(p[43]), .P44(p[44]), .P45(p[45]), .P46(p[46]), .P47(p[47]),
    .ACOUT0(acout[0]), .ACOUT1(acout[1]), .ACOUT2(acout[2]), .ACOUT3(acout[3]), .ACOUT4(acout[4]), .ACOUT5(acout[5]),
    .ACOUT6(acout[6]), .ACOUT7(acout[7]), .ACOUT8(acout[8]), .ACOUT9(acout[9]), .ACOUT10(acout[10]), .ACOUT11(acout[11]),
    .ACOUT12(acout[12]), .ACOUT13(acout[13]), .ACOUT14(acout[14]), .ACOUT15(acout[15]), .ACOUT16(acout[16]), .ACOUT17(acout[17]),
    .ACOUT18(acout[18]), .ACOUT19(acout[19]), .ACOUT20(acout[20]), .ACOUT21(acout[21]), .ACOUT22(acout[22]), .ACOUT23(acout[23]),
    .ACOUT24(acout[24]), .ACOUT25(acout[25]), .ACOUT26(acout[26]), .ACOUT27(acout[27]), .ACOUT28(acout[28]), .ACOUT29(acout[29]));
endmodule

module tb_dsp_reg;
  localparam N = 40;               // edges per run
  reg clk;
  reg [29:0] a; reg [17:0] b; reg [47:0] c;
  reg cea1, cea2, ceb1, ceb2, cec, cem, cep, rsta, rstb, rstc, rstm, rstp;
  // per-edge stimulus: index e = the value present at rising edge e (1..N)
  reg [29:0] A [0:N+1]; reg [17:0] B [0:N+1]; reg [47:0] C [0:N+1];
  integer e, k, fails = 0, checks = 0, seed = 7;

  // configurations under test (one instance each, all on the same stimulus)
  wire [47:0] p0, p1, p2, p3, p4, p5, p6, p7, p8, p9;
  wire [29:0] ac0, ac1, ac2, ac3, ac4, ac5, ac6, ac7, ac8, ac9;
  // 0: the probe's AREG=1 cell: AREG=1/ACASCREG=1 BREG=1 MREG=1      LA=2 LB=2
  dut_wrap #(.AREG(1), .ACASCREG(1), .BREG(1), .BCASCREG(1), .MREG(1)) d0 (clk, a, b, c, 1'b0, 1'b1, 1'b0, 1'b1, 1'b0, 1'b1, 1'b0, 1'b0,1'b0,1'b0,1'b0,1'b0, p0, ac0);
  // 1: what the unpatched bits decode to: AREG=2/ACASCREG=1, same CE wiring (CEA1=0!)
  dut_wrap #(.AREG(2), .ACASCREG(1), .BREG(2), .BCASCREG(1), .MREG(1)) d1 (clk, a, b, c, 1'b0, 1'b1, 1'b0, 1'b1, 1'b0, 1'b1, 1'b0, 1'b0,1'b0,1'b0,1'b0,1'b0, p1, ac1);
  // 2: AREG=2/ACASCREG=1 with every CE on                               LA=3 LB=3
  dut_wrap #(.AREG(2), .ACASCREG(1), .BREG(2), .BCASCREG(1), .MREG(1)) d2 (clk, a, b, c, 1'b1, 1'b1, 1'b1, 1'b1, 1'b0, 1'b1, 1'b0, 1'b0,1'b0,1'b0,1'b0,1'b0, p2, ac2);
  // 3: AREG=2/ACASCREG=2, BREG=0, MREG=0, PREG=1                         LA=3 LB=1
  dut_wrap #(.AREG(2), .ACASCREG(2), .PREG(1)) d3 (clk, a, b, c, 1'b1, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b1, 1'b0,1'b0,1'b0,1'b0,1'b0, p3, ac3);
  // 4: AREG=0, BREG=1, CREG=1, Z=C: P = A*B + C                         LA=0 LB=1 LC=1
  dut_wrap #(.BREG(1), .BCASCREG(1), .CREG(1), .ZMUX(3)) d4 (clk, a, b, c, 1'b0, 1'b0, 1'b0, 1'b1, 1'b1, 1'b0, 1'b0, 1'b0,1'b0,1'b0,1'b0,1'b0, p4, ac4);
  // 5: AREG=2 with INMODE[0]=1 (multiplier reads A1), MREG=1             LA=2 LB=1
  dut_wrap #(.AREG(2), .ACASCREG(2), .MREG(1), .ASEL1(1)) d5 (clk, a, b, c, 1'b1, 1'b1, 1'b0, 1'b0, 1'b0, 1'b1, 1'b0, 1'b0,1'b0,1'b0,1'b0,1'b0, p5, ac5);
  // 6: the probe's AREG=1 cell with IS_CLK_INVERTED: loads on the falling edge
  dut_wrap #(.AREG(1), .ACASCREG(1), .BREG(1), .BCASCREG(1), .MREG(1), .CLKINV(1)) d6 (clk, a, b, c, 1'b0, 1'b1, 1'b0, 1'b1, 1'b0, 1'b1, 1'b0, 1'b0,1'b0,1'b0,1'b0,1'b0, p6, ac6);
  // 7: PREG accumulator, Z=P: P(e) = P(e-1) + A(e)*B(e)
  dut_wrap #(.PREG(1), .ZMUX(2)) d7 (clk, a, b, c, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b1, 1'b0,1'b0,1'b0,1'b0,1'b0, p7, ac7);
  // 8: CE and RST: AREG=2/ACASCREG=1 MREG=1, driven by cea1..rstm below
  dut_wrap #(.AREG(2), .ACASCREG(1), .MREG(1)) d8 (clk, a, b, c, cea1, cea2, 1'b0, 1'b0, 1'b0, cem, 1'b0, rsta, 1'b0, 1'b0, rstm, 1'b0, p8, ac8);
  // 9: CE and RST on AREG=1 (CEA2 is the A register's enable)
  dut_wrap #(.AREG(1), .ACASCREG(1), .MREG(0)) d9 (clk, a, b, c, cea1, cea2, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, rsta, 1'b0, 1'b0, 1'b0, 1'b0, p9, ac9);

  function [47:0] mul(input [29:0] x, input [17:0] y);
    reg signed [24:0] xs; reg signed [17:0] ys; reg signed [47:0] r;
    begin xs = x[24:0]; ys = y; r = xs * ys; mul = r; end
  endfunction
  function [29:0] Aat(input integer i); Aat = (i < 1) ? 30'd0 : A[i]; endfunction  // registers power up 0
  function [17:0] Bat(input integer i); Bat = (i < 1) ? 18'd0 : B[i]; endfunction
  function [47:0] Cat(input integer i); Cat = (i < 1) ? 48'd0 : C[i]; endfunction

  task chk(input [8*24-1:0] what, input integer ee, input [47:0] got, input [47:0] want);
    begin
      checks = checks + 1;
      if (got !== want) begin
        fails = fails + 1;
        if (fails < 30) $display("  MISMATCH %0s before edge %0d: got %h want %h", what, ee, got, want);
      end
    end
  endtask

  // references for runs 7/8/9, stated register by register from UG479
  reg [29:0] r8a1, r8a2, r9a2, o1, o2; reg [42:0] r8m; reg [47:0] acc7, mm;
  initial clk = 1;
  always #5000 clk = ~clk;          // rising edge e at t = 10000*e, falling at 10000*e - 5000
  initial begin
    for (k = 0; k <= N+1; k = k + 1) begin
      A[k] = {$random(seed)} & 30'h1ffffff; B[k] = $random(seed); C[k] = {$random(seed), $random(seed)};
      // never a zero operand: "frozen at 0" and "late" must look different
      if (A[k][24:0] == 0) A[k] = 30'd12345;
      if (B[k] == 0) B[k] = 18'd321;
    end
    r8a1 = 0; r8a2 = 0; r8m = 0; r9a2 = 0; acc7 = 0;
    a = 0; b = 0; c = 0; {cea1, cea2, cem, rsta, rstm} = 5'b11100;
    for (e = 1; e <= N; e = e + 1) begin
      // the inputs of rising edge e: set 3 ns before it, held 10 ns (so the
      // falling edge 5 ns after it samples them too)
      #(10000*e - 3000 - $time);
      a = A[e]; b = B[e]; c = C[e];
      cea1 = !(e % 5 == 2);  cea2 = !(e % 7 == 3);  cem = !(e % 11 == 4);
      rsta = (e == 19 || e == 33); rstm = (e == 23);   // both with their CEs on (RST over CE)
      #2000;                 // 1 ns before rising edge e: registers hold edge e-1's loads
      if (e > 4) begin
        chk("d0 AREG1 MREG1 L2", e, p0, mul(Aat(e-2), Bat(e-2)));
        chk("d1 AREG2 CEA1=0", e, p1, 48'd0);           // A1/B1 never load: M = 0
        chk("d2 AREG2 MREG1 L3", e, p2, mul(Aat(e-3), Bat(e-3)));
        chk("d2 ACOUT=A1", e, {18'd0, ac2}, {18'd0, Aat(e-1)});
        chk("d3 AREG2 PREG L3/1", e, p3, mul(Aat(e-3), Bat(e-1)));
        chk("d3 ACOUT=A2", e, {18'd0, ac3}, {18'd0, Aat(e-2)});
        chk("d0 ACOUT=A2", e, {18'd0, ac0}, {18'd0, Aat(e-1)});
        chk("d1 ACOUT=A1=0", e, {18'd0, ac1}, 48'd0);
        chk("d4 BREG CREG Z=C", e, p4, mul(Aat(e), Bat(e-1)) + Cat(e-1));
        chk("d5 AREG2 ASEL1 L2", e, p5, mul(Aat(e-2), Bat(e-1)));
        chk("d7 PREG accum", e, p7, acc7);
        chk("d8 CE/RST M", e, p8, {{5{r8m[42]}}, r8m});
        chk("d8 CE/RST ACOUT=A1", e, {18'd0, ac8}, {18'd0, r8a1});
        chk("d9 CE/RST AREG1", e, p9, mul(r9a2, Bat(e)));
      end
      #500;
      // edge e's loads, on the reference (synchronous, RST over CE, every
      // register reads its source's value from BEFORE the edge)
      o1 = r8a1; o2 = r8a2;
      if (rstm) r8m = 0; else if (cem) begin mm = mul(o2, B[e]); r8m = mm[42:0]; end
      if (rsta) begin r8a1 = 0; r8a2 = 0; end
      else begin if (cea2) r8a2 = o1; if (cea1) r8a1 = A[e]; end
      if (rsta) r9a2 = 0; else if (cea2) r9a2 = A[e];
      acc7 = acc7 + mul(A[e], B[e]);
      // 3 ns after rising edge e, before the falling edge: the CLKINV run last
      // loaded on the falling edge 5 ns BEFORE edge e (inputs of edge e-1)
      #3500;
      if (e > 4) begin
        chk("d6 CLKINV L2 (fall)", e, p6, mul(Aat(e-2), Bat(e-2)));
        chk("d0 rise, same time", e, p0, mul(Aat(e-1), Bat(e-1)));
      end
    end
    $display("DSPREG %s  (%0d checks, %0d mismatches)", fails ? "FAIL" : "PASS", checks, fails);
    $finish;
  end
endmodule
