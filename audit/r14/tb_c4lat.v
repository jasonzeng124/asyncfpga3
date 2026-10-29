// audit r14: CARRY4 and SLICE_LATX early-edge check, own reference.
// Random pin traces on a 10 ps grid, arcs multiples of 10 ps (random per pin/output);
// reference = UG474 equations / latch function on per-arc transport-delayed copies,
// built in this TB. Outputs compared at every 10k+5 ps.
`timescale 1ps/1ps
module tb_c4lat;
  parameter integer SEEDP = 1;
  integer seed, i, n, mis_o0, mis_o1, mis_co1, mis_lq, nchk;
  reg CIN=0, S0=0, S1=0, DI0=0, DI1=0;
  reg LCK=0, LD=0;
  // arcs (ps, multiples of 10), deliberately far apart so SAF early edges show
  localparam integer A_CIN_O0=400, A_S0_O0=50, A_CIN_O1=150, A_S0_O1=330, A_S1_O1=60, A_DI0_O1=210,
                     A_CIN_CO1=90, A_S0_CO1=420, A_S1_CO1=270, A_DI0_CO1=40, A_DI1_CO1=310;
  localparam integer L_CK=300, L_D=60;
  wire O0, O1, O2, O3, CO0, CO1, CO2, CO3, LQ;
  CARRY4 #(.TCINO0(A_CIN_O0), .TS0O0(A_S0_O0), .TCINO1(A_CIN_O1), .TS0O1(A_S0_O1), .TS1O1(A_S1_O1),
           .TDI0O1(A_DI0_O1), .TCINCO1(A_CIN_CO1), .TS0CO1(A_S0_CO1), .TS1CO1(A_S1_CO1),
           .TDI0CO1(A_DI0_CO1), .TDI1CO1(A_DI1_CO1)) c (
    .CIN(CIN), .CYINIT(1'b0), .DI0(DI0), .DI1(DI1), .DI2(1'b0), .DI3(1'b0),
    .S0(S0), .S1(S1), .S2(1'b0), .S3(1'b0),
    .O0(O0), .O1(O1), .O2(O2), .O3(O3), .CO0(CO0), .CO1(CO1), .CO2(CO2), .CO3(CO3));
`ifdef GLS_FID
  SLICE_LATX #(.TCKQ(L_CK), .TDQ(L_D)) l (.CK(LCK), .D(LD), .CE(1'b1), .SR(1'b0), .Q(LQ));
`else
  SLICE_LATX #(.TCKQ(L_CK)) l (.CK(LCK), .D(LD), .CE(1'b1), .SR(1'b0), .Q(LQ));
`endif
  // reference copies
  reg r_cin_o0=0, r_s0_o0=0, r_cin_o1=0, r_s0_o1=0, r_s1_o1=0, r_di0_o1=0;
  reg r_cin_co1=0, r_s0_co1=0, r_s1_co1=0, r_di0_co1=0, r_di1_co1=0, r_ck=0, r_d=0, r_q=0;
  always @(CIN) begin r_cin_o0 <= #(A_CIN_O0) CIN; r_cin_o1 <= #(A_CIN_O1) CIN; r_cin_co1 <= #(A_CIN_CO1) CIN; end
  always @(S0)  begin r_s0_o0 <= #(A_S0_O0) S0; r_s0_o1 <= #(A_S0_O1) S0; r_s0_co1 <= #(A_S0_CO1) S0; end
  always @(S1)  begin r_s1_o1 <= #(A_S1_O1) S1; r_s1_co1 <= #(A_S1_CO1) S1; end
  always @(DI0) begin r_di0_o1 <= #(A_DI0_O1) DI0; r_di0_co1 <= #(A_DI0_CO1) DI0; end
  always @(DI1) r_di1_co1 <= #(A_DI1_CO1) DI1;
  always @(LCK) r_ck <= #(L_CK) LCK;
  always @(LD)  r_d  <= #(L_D) LD;
  always @(r_ck or r_d) if (r_ck) r_q = r_d;
  wire e_o0  = r_s0_o0 ^ r_cin_o0;
  wire e_o1  = r_s1_o1 ^ (r_s0_o1 ? r_cin_o1 : r_di0_o1);
  wire e_co1 = r_s1_co1 ? (r_s0_co1 ? r_cin_co1 : r_di0_co1) : r_di1_co1;
  initial begin
    seed = SEEDP; mis_o0 = 0; mis_o1 = 0; mis_co1 = 0; mis_lq = 0; nchk = 0;
    if ($value$plusargs("SEED=%d", seed)) ;
    #2000;
    fork
      begin
        for (i = 0; i < 4000; i = i + 1) begin
          #(10 * (1 + {$random(seed)} % 12));
          n = {$random(seed)} % 7;
          case (n) 0: CIN = ~CIN; 1: S0 = ~S0; 2: S1 = ~S1; 3: DI0 = ~DI0; 4: DI1 = ~DI1;
                   5: LCK = ~LCK; 6: LD = ~LD; endcase
        end
        #2000;
      end
      begin
        #5;
        repeat (40000) begin
          #10;
          if ($time > 3000) begin
            nchk = nchk + 1;
            if (O0 !== e_o0) mis_o0 = mis_o0 + 1;
            if (O1 !== e_o1) mis_o1 = mis_o1 + 1;
            if (CO1 !== e_co1) mis_co1 = mis_co1 + 1;
            if (LQ !== r_q) mis_lq = mis_lq + 1;
          end
        end
      end
    join
    $display("C4LAT seed=%0d checks=%0d mismatches O0=%0d O1=%0d CO1=%0d LQ=%0d", seed, nchk, mis_o0, mis_o1, mis_co1, mis_lq);
    $finish;
  end
endmodule
