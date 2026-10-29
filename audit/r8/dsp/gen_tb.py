"""Auditor (r8): compare research prims.v DSP48E1_DSP48E1 (params from research
dsp_model.config) against yosys cells_sim DSP48E1 (all regs 0) on random vectors.
usage: python3 -I gen_tb.py <research cells/gls dir> > tb_dsp.v"""
import sys, random
sys.path.insert(0, sys.argv[1]); import dsp_model
random.seed(8)
cases = []
# (name, opmode, alumode, inmode, carryinsel, carryin)
for z in (0, 1, 5):
    cases.append(("mul_z%d" % z, (z << 4) | 0b0101, 0, 0, 0, 0))
for alu in (0, 1, 2, 3):
    for cin in (0, 1):
        cases.append(("mul_zC_alu%d_cin%d" % (alu, cin), (3 << 4) | 0b0101, alu, 0, 0, cin))
        cases.append(("AB_C_zPCIN_alu%d_cin%d" % (alu, cin), (1 << 4) | 0b1111, alu, 0, 0, cin))
        cases.append(("AB_ones_zC_alu%d_cin%d" % (alu, cin), (3 << 4) | 0b1011, alu, 0, 0, cin))
        cases.append(("AB_0_zPCINsh_alu%d_cin%d" % (alu, cin), (5 << 4) | 0b0011, alu, 0, 0, cin))
        cases.append(("gated_mul_zC_alu%d_cin%d" % (alu, cin), (3 << 4) | 0b0101, alu, 0b00010, 0, cin))
for alu in (4, 5, 6, 7, 12, 13, 14, 15):
    for y in (0, 2):
        cases.append(("logic_AB_y%d_zC_alu%d" % (y, alu), (3 << 4) | (y << 2) | 3, alu, 0, 0, 0))
        cases.append(("logic_0_y%d_zPCIN_alu%d" % (y, alu), (1 << 4) | (y << 2) | 0, alu, 0, 0, 0))
    cases.append(("MUNK_gatedM_zC_alu%d" % alu, (3 << 4) | 0b0101, alu, 0b11111, 0, 0))
    cases.append(("MUNK_gatedM_zP_alu%d" % alu, (2 << 4) | 0b0101, alu, 0b11111, 0, 0))
# refusals expected
cases += [("ref_ungated_logicM", (3 << 4) | 0b0101, 12, 0, 0, 0),
          ("ref_alu8", (3 << 4) | 0b0011, 8, 0, 0, 0),
          ("ref_cinsel", (3 << 4) | 0b0011, 0, 0, 1, 0),
          ("ref_zP_arith", (2 << 4) | 0b0011, 0, 0, 0, 0),
          ("ref_logic_yC", (0 << 4) | 0b1111, 12, 0, 0, 0),
          ("ref_inmode0", (0 << 4) | 0b0101, 0, 1, 0, 0),
          ("ref_X_M_only", 0b0001, 0, 0, 0, 0),
          ("ok_logic_zP_const", (2 << 4) | 0b0000, 12, 0, 0, 0)]
N = 400
out = []; W = out.append
W("`timescale 1ps/1ps\nmodule tb;\n  reg [29:0] A; reg [17:0] B; reg [47:0] C, PCIN;\n  integer i, bad, xs;")
names = []
for k, (nm, op, al, inm, cs, ci) in enumerate(cases):
    p, why = dsp_model.config(op, al, inm, cs, ci)
    sys.stderr.write("%-28s OP=%s ALU=%s IN=%s CS=%d CI=%d -> %s\n" % (nm, format(op, "07b"), format(al, "04b"),
                     format(inm, "05b"), cs, ci, ("REFUSED: " + "; ".join(why)) if why else
                     "model %s" % {k2: p[k2] for k2 in ("XMUX", "YMUX", "ZMUX", "ALUMODE", "AGATE", "CIN", "MUNK")}))
    if why:
        continue
    names.append((k, nm, p["MUNK"]))
    W("  wire [47:0] PR%d, PY%d;" % (k, k))
    W("  DSP48E1 #(.ACASCREG(0),.ADREG(0),.ALUMODEREG(0),.AREG(0),.BCASCREG(0),.BREG(0),.CARRYINREG(0),"
      ".CARRYINSELREG(0),.CREG(0),.DREG(0),.INMODEREG(0),.MREG(0),.OPMODEREG(0),.PREG(0)) Y%d ("
      ".A(A),.B(B),.C(C),.PCIN(PCIN),.ACIN(30'd0),.BCIN(18'd0),.D(25'd0),.CARRYCASCIN(1'b0),.MULTSIGNIN(1'b0),"
      ".CLK(1'b0),.OPMODE(7'd%d),.ALUMODE(4'd%d),.INMODE(5'd%d),.CARRYINSEL(3'd%d),.CARRYIN(1'b%d),.P(PY%d),"
      ".CEA1(1'b0),.CEA2(1'b0),.CEAD(1'b0),.CEALUMODE(1'b0),.CEB1(1'b0),.CEB2(1'b0),.CEC(1'b0),.CECARRYIN(1'b0),"
      ".CECTRL(1'b0),.CED(1'b0),.CEINMODE(1'b0),.CEM(1'b0),.CEP(1'b0),.RSTA(1'b0),.RSTALLCARRYIN(1'b0),"
      ".RSTALUMODE(1'b0),.RSTB(1'b0),.RSTC(1'b0),.RSTCTRL(1'b0),.RSTD(1'b0),.RSTINMODE(1'b0),.RSTM(1'b0),.RSTP(1'b0));"
      % (k, op, al, inm, cs, ci, k))
    conn = [".A%d(A[%d])" % (i, i) for i in range(30)] + [".ACIN%d(1'b0)" % i for i in range(30)] + \
           [".B%d(B[%d])" % (i, i) for i in range(18)] + [".C%d(C[%d])" % (i, i) for i in range(48)] + \
           [".PCIN%d(PCIN[%d])" % (i, i) for i in range(48)] + [".P%d(PR%d[%d])" % (i, k, i) for i in range(48)]
    prm = ".ZMUX(%d), .ACASC(0), .XMUX(%d), .YMUX(%d), .ALUMODE(%d), .AGATE(%d), .CIN(%d), .MUNK(%d)" % (
        p["ZMUX"], p["XMUX"], p["YMUX"], p["ALUMODE"], p["AGATE"], p["CIN"], p["MUNK"])
    if dsp_model.is_default(p):
        prm = ".ZMUX(%d), .ACASC(0)" % p["ZMUX"]
    W("  DSP48E1_DSP48E1 #(%s) R%d (%s);" % (prm, k, ", ".join(conn)))
W("  initial begin")
W("    for (i = 0; i < %d; i = i + 1) begin" % N)
W("      A = {$random, $random}; B = $random; C = {$random, $random}; PCIN = {$random, $random};")
W("      if (i == 0) begin A = 0; B = 0; C = 0; PCIN = 0; end")
W("      if (i == 1) begin A = -1; B = -1; C = -1; PCIN = -1; end")
W("      #5000;")
for k, nm, munk in names:
    W("      if (PR%d !== PY%d) begin bad_%d = bad_%d + 1; if (bad_%d <= 2) $display(\"MISMATCH %s i=%%0d A=%%h B=%%h C=%%h PCIN=%%h research=%%h yosys=%%h\", i, A, B, C, PCIN, PR%d, PY%d); end"
      % (k, k, k, k, k, nm, k, k))
    W("      if (^PR%d === 1'bx) xs_%d = xs_%d + 1;" % (k, k, k))
W("    end")
for k, nm, munk in names:
    W("    $display(\"%-28s mismatches=%%0d/%d  research_x_vectors=%%0d  MUNK=%d\", bad_%d, xs_%d);" % (nm, N, munk, k, k))
W("    $finish;\n  end")
for k, nm, munk in names:
    out.insert(1, "  integer bad_%d = 0, xs_%d = 0;" % (k, k))
W("endmodule")
print("\n".join(out))
