"""Auditor (r13): research prims.v DSP48E1_DSP48E1 (registered, params from
research dsp_model.config/reg_config) vs yosys cells_sim DSP48E1
(audit/r8/dsp/yosys_dsp48e1.v = cells_sim.v with $fatal -> $display),
random A/B/C/PCIN/ACIN and random CE/RST every cycle.
usage: python3 -I gen_reg_tb.py <research cells/gls dir> <part k of n> > tb.v
Compares P and ACOUT 1 ns after each rising edge and 1 ns before the next."""
import sys, random, itertools
sys.path.insert(0, sys.argv[1]); import dsp_model
part, nparts = (int(x) for x in sys.argv[2].split("/"))
random.seed(13)
AOPT = [(0, 0), (1, 1), (2, 1), (2, 2)]
ops = [  # name, opmode, alumode, inmode, cin, needs_preg
    ("mul", 0x05, 0, 0, 0, 0),
    ("mulC", 0x35, 0, 0, 0, 0),
    ("mulPCIN_sub_cin", 0x15, 3, 0, 1, 0),
    ("mulA1B1", 0x05, 0, 0b10001, 0, 0),
    ("mulA1", 0x35, 0, 0b00001, 0, 0),
    ("AB_C_add", 0x33, 0, 0, 1, 0),
    ("AB_ones_C_alu1", 0x3B, 1, 0, 0, 0),
    ("logic_AB_xor_C", 0x33, 4, 0, 0, 0),
    ("macc", 0x25, 0, 0, 0, 1),
    ("XP_C", 0x0E, 0, 0, 0, 1),
    ("P_shift17_mul", 0x65, 0, 0, 0, 1),
    ("gated_C", 0x35, 0, 0b00010, 0, 0),
]
cases = []
for (ar, ac), (br, bc), cr, mr, pr in itertools.product(AOPT, AOPT, (0, 1), (0, 1), (0, 1)):
    for nm, op, al, inm, ci, np in ops:
        if np and not pr:
            continue
        if not any((ar, br, cr, mr, pr)):
            continue
        cases.append((nm, op, al, inm, ci, dict(AREG=ar, ACASCREG=ac, BREG=br, BCASCREG=bc,
                                                  CREG=cr, MREG=mr, PREG=pr), 0, 0))
# a few with CLKINV and with A_INPUT=CASCADE
for k in range(24):
    nm, op, al, inm, ci, np = ops[k % len(ops)]
    ar, ac = AOPT[k % 4]; br, bc = AOPT[(k // 4) % 4]
    cases.append((nm, op, al, inm, ci, dict(AREG=ar, ACASCREG=ac, BREG=br, BCASCREG=bc, CREG=k & 1,
                                              MREG=(k >> 1) & 1, PREG=1), k & 1, (k >> 1) & 1))
cases = cases[part::nparts]
N = 300
W = []
W.append("`timescale 1ps/1ps\nmodule tb;\n  reg clk = 0; integer t, bad, xr, xy, nx;")
W.append("  reg [29:0] A, ACIN; reg [17:0] B; reg [47:0] C, PCIN;")
W.append("  reg CEA1, CEA2, CEB1, CEB2, CEC, CEM, CEP, RSTA, RSTB, RSTC, RSTM, RSTP;")
names = []
for k, (nm, op, al, inm, ci, regs, clkinv, acasc) in enumerate(cases):
    rp, pins, rwhy = dsp_model.reg_config(regs)
    p, why = dsp_model.config(op, al, inm, 0, ci, rp)
    tag = "%s %s CLKINV=%d ACASC=%d" % (nm, " ".join("%s=%d" % (x, rp[x]) for x in dsp_model.REGS), clkinv, acasc)
    if rwhy or why:
        sys.stderr.write("REFUSED %s: %s\n" % (tag, "; ".join(rwhy + why)))
        continue
    names.append((k, tag))
    rpar = ", ".join(".%s(%d)" % (x, p[x]) for x in ("XMUX", "YMUX", "ALUMODE", "AGATE", "CIN", "MUNK")
                     + dsp_model.REG_PARAMS)
    pinsR = [".%s%d(%s[%d])" % ("ACIN" if acasc else "A", i, "ACIN" if acasc else "A", i) for i in range(30)]
    pinsR += [".B%d(B[%d])" % (i, i) for i in range(18)]
    pinsR += [".C%d(C[%d])" % (i, i) for i in range(48)]
    pinsR += [".PCIN%d(PCIN[%d])" % (i, i) for i in range(48)]
    pinsR += [".P%d(PR%d[%d])" % (i, k, i) for i in range(48)]
    pinsR += [".ACOUT%d(AR%d[%d])" % (i, k, i) for i in range(30)]
    pinsR += [".%s(%s)" % (q, q) for q in pins if q != "CLK"] + [".CLK(clk)"]
    W.append("  wire [47:0] PR%d, PY%d; wire [29:0] AR%d, AY%d;" % (k, k, k, k))
    W.append("  DSP48E1_DSP48E1 #(.ZMUX(%d), .ACASC(%d), %s, .CLKINV(%d)) R%d (%s);"
             % (p["ZMUX"], acasc, rpar, clkinv, k, ", ".join(pinsR)))
    yp = ",".join(".%s(%d)" % (x, rp[x]) for x in dsp_model.REGS)
    W.append("  DSP48E1 #(%s,.A_INPUT(\"%s\"),.ADREG(0),.ALUMODEREG(0),.CARRYINREG(0),.CARRYINSELREG(0),.DREG(0),"
             ".INMODEREG(0),.OPMODEREG(0)) Y%d (.A(A),.B(B),.C(C),.PCIN(PCIN),.ACIN(ACIN),.BCIN(18'd0),.D(25'd0),"
             ".CARRYCASCIN(1'b0),.MULTSIGNIN(1'b0),.CLK(%sclk),.OPMODE(7'd%d),.ALUMODE(4'd%d),.INMODE(5'd%d),"
             ".CARRYINSEL(3'd0),.CARRYIN(1'b%d),.P(PY%d),.ACOUT(AY%d),.CEA1(CEA1),.CEA2(CEA2),.CEAD(1'b0),"
             ".CEALUMODE(1'b0),.CEB1(CEB1),.CEB2(CEB2),.CEC(CEC),.CECARRYIN(1'b0),.CECTRL(1'b0),.CED(1'b0),"
             ".CEINMODE(1'b0),.CEM(CEM),.CEP(CEP),.RSTA(RSTA),.RSTALLCARRYIN(1'b0),.RSTALUMODE(1'b0),.RSTB(RSTB),"
             ".RSTC(RSTC),.RSTCTRL(1'b0),.RSTD(1'b0),.RSTINMODE(1'b0),.RSTM(RSTM),.RSTP(RSTP));"
             % (yp, "CASCADE" if acasc else "DIRECT", k, "~" if clkinv else "", op, al, inm, ci, k, k))
W.append("  task chk(input integer ph); begin")
for k, tag in names:
    W.append("    if (PY%d !== PR%d || AY%d !== AR%d) begin"
             " if ((^PY%d) === 1'bx || (^AY%d) === 1'bx) xy = xy + 1;"
             " else if ((^PR%d) === 1'bx || (^AR%d) === 1'bx) xr = xr + 1; else bad = bad + 1;"
             " if (nx < 400) $display(\"MISMATCH k=%d t=%%0d ph=%%0d P y=%%h r=%%h ACOUT y=%%h r=%%h [%s]\", t, ph, PY%d, PR%d, AY%d, AR%d);"
             " nx = nx + 1; end" % (k, k, k, k, k, k, k, k, k, tag, k, k, k, k))
W.append("  end endtask")
W.append("  initial begin bad = 0; xr = 0; xy = 0; nx = 0;")
W.append("    A = 0; ACIN = 0; B = 0; C = 0; PCIN = 0; {CEA1,CEA2,CEB1,CEB2,CEC,CEM,CEP} = 0; {RSTA,RSTB,RSTC,RSTM,RSTP} = 0;")
W.append("    for (t = 0; t < %d; t = t + 1) begin" % N)
W.append("      #2000; A = {$random, $random}; ACIN = {$random}; B = $random; C = {$random, $random}; PCIN = {$random, $random};")
W.append("      CEA1 = ($random & 3) != 0; CEA2 = ($random & 3) != 0; CEB1 = ($random & 3) != 0; CEB2 = ($random & 3) != 0;")
W.append("      CEC = ($random & 3) != 0; CEM = ($random & 3) != 0; CEP = ($random & 3) != 0;")
W.append("      RSTA = ($random & 15) == 0; RSTB = ($random & 15) == 0; RSTC = ($random & 15) == 0;")
W.append("      RSTM = ($random & 15) == 0; RSTP = ($random & 15) == 0;")
W.append("      #2000; chk(0);")             # 1 ns before the rising edge at 5 ns
W.append("      #1000; clk = 1; #1000; chk(1); #4000; clk = 0;")
W.append("    end")
W.append("    $display(\"SUMMARY configs=%d cycles=%d mismatches(determined)=%%0d research_x_only=%%0d yosys_x=%%0d\", bad, xr, xy);" % (len(names), N))
W.append("    $finish;\n  end\nendmodule")
print("\n".join(W))
sys.stderr.write("modelled configs: %d\n" % len(names))
