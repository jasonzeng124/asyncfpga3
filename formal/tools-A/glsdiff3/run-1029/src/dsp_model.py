"""DSP48E1 configurations that prims.v's DSP48E1_DSP48E1 models.

One decision, shared by gen.py (routed JSON or bits-built JSON) and
fid/fasm2net.py (the bits): given the decoded control words of a DSP48E1
(and, since S7, its pipeline-register parameters), either the model
parameters that simulate it, or the reasons it is refused.  A refusal is
better than a mis-simulation.  With every register off (regs=None) the
decision is exactly the combinational one it always was.

REGISTERS (S7; reg_config() below).  Modelled: AREG/BREG 0/1/2 with
ACASCREG/BCASCREG (UG479 Table 2-1: AREG=0 -> ACASCREG=0, AREG=1 ->
ACASCREG=1, AREG=2 -> ACASCREG 1 or 2), CREG, MREG, PREG, each 0/1, clocked
by CLK (IS_CLK_INVERTED), with CEA1/CEA2/CEB1/CEB2/CEC/CEM/CEP and
RSTA/RSTB/RSTC/RSTM/RSTP.  Semantics, as UG479 states them and as yosys
techlibs/xilinx/cells_sim.v DSP48E1 implements them (cross-read; the UG479
PDF was not reachable from this machine):
  * every register is a rising-edge (falling with IS_CLK_INVERTED) flop
    that powers up 0 (GSR); its RST is SYNCHRONOUS and has priority over its
    CE; CE=0 holds.
  * A: AREG=2 is A1 (CEA1) then A2 (CEA2, loads A1).  AREG=1 is the A2
    register loading A directly (CEA2); the A1 register still exists on CEA1
    (UG479: "A1 is only used if AREG=2 or INMODE[0]=1").  AREG=0 bypasses
    both.  RSTA clears both.  The multiplier's A operand is INMODE[0] ? A1 :
    A2; the X mux's A:B concatenation is A2:B2.  ACOUT is A1 when AREG=2 and
    ACASCREG=1, else A2 (the A input when AREG=0).  B: the same with
    CEB1/CEB2/RSTB and INMODE[4] (BCOUT is not a modelled output).
  * C: CREG (CEC, RSTC) feeds both the Y and Z C inputs.  M: MREG (CEM,
    RSTM) registers the multiplier output.  P: PREG (CEP, RSTP) registers
    the ALU output; with PREG=1, OPMODE X=10 (P), Z=010 (P) and Z=110
    (P>>>17) read that register and are modelled.
Still REFUSED: ADREG, DREG, INMODEREG, OPMODEREG, ALUMODEREG, CARRYINREG,
CARRYINSELREG = 1 (a registered control word powers up 0 and needs its CE:
not modelled), Z=100 (P, MACC extend), USE_DPORT, any AREG/ACASCREG pair
outside UG479's table, INMODE[0]/[4] with that side's register at 0 and A
not gated (as before), and INMODE[2]/[3] (pre-adder) with A not gated.

Semantics (UG479, 7 Series DSP48E1 User Guide; the PDF was not reachable from
this machine, so the tables below are the ones this code was written from,
cross-read against yosys techlibs/xilinx/cells_sim.v DSP48E1):

  INMODE (Table 2-7)  INMODE[1]=1 gates the multiplier's A operand to zero.
      INMODE[0]/[4] pick A1/A2 and B1/B2; with AREG=BREG=0 there is no A1/B1
      register, so they are refused unless the A operand is gated (then M is
      zero whatever A or B is).  INMODE[2]/[3] (D enable, pre-adder subtract)
      act on the pre-adder, which USE_DPORT=FALSE bypasses (the multiplier
      reads the gated A directly); refused unless A is gated, same reason.
      ASSUMPTION: with USE_DPORT=FALSE the pre-adder/D path never reaches the
      multiplier (UG479 USE_DPORT; yosys cells_sim agrees).
  OPMODE (Tables 2-8..2-10)  X[1:0]: 00 0, 01 M, 10 P, 11 A:B.
      Y[3:2]: 00 0, 01 M, 10 all ones, 11 C.   Z[6:4]: 000 0, 001 PCIN,
      010 P, 011 C, 100 P, 101 PCIN>>>17, 110 P>>>17, 111 illegal.
      M must be selected on X and Y together (two partial products).
  ALUMODE (Tables 2-13, 2-14)  arithmetic 0000 Z+X+Y+CIN, 0001 ~Z+X+Y+CIN,
      0010 ~(Z+X+Y+CIN), 0011 Z-(X+Y+CIN); logic (Y = 0 or all ones only)
      01xx/11xx as the two-input tables.  Modelled by the three-input
      carry-save structure those tables come from (alu() below and prims.v).

Refused: X=P or Z=P with PREG=0 (a combinational loop) UNLESS the output is
provably independent of Z (X and Y constants and a logic mode whose result
does not change between Z=0 and Z=~0, e.g. X AND Z with X=0); a logic mode
reading the multiplier with A not gated.  A logic mode reading a GATED
multiplier (the unpatched constpins writers' INMODE 11111 / ALUMODE 11xx /
OPMODE M on X and Y) is simulated as UNKNOWN (MUNK=1: every output bit x):
the multiplier hands the ALU two partial products whose SUM is A*B, and with
A gated only the sum is known to be 0, not each word, so X AND Z etc. is not
determined by UG479.  The board ran this configuration and got 965/2016 ipow
products right, which "both partial products 0" (every output 0) cannot give; ALUMODE 10xx (not in UG479's tables);
CARRYINSEL other than 000; CARRYIN=1 in a logic mode; Z=111.
"""

MASK = (1 << 48) - 1
DEFAULT = {"XMUX": 1, "YMUX": 1, "ALUMODE": 0, "AGATE": 0, "CIN": 0, "MUNK": 0}


def alu(x, y, z, alumode, cin):
    """The ALU as prims.v computes it (48-bit words, unsigned)."""
    zi = (~z & MASK) if alumode & 1 else z
    s = x ^ y ^ zi
    c = (x & y) | (x & zi) | (y & zi)
    smux = c if alumode & 8 else s
    cmux = 0 if alumode & 4 else c
    r = (smux + (cmux << 1) + cin) & MASK
    return (~r & MASK) if alumode & 2 else r


REGS = ("AREG", "ACASCREG", "BREG", "BCASCREG", "CREG", "MREG", "PREG")
REGS_REFUSED = ("ADREG", "DREG", "INMODEREG", "OPMODEREG", "ALUMODEREG", "CARRYINREG", "CARRYINSELREG")
# the clock-enable / reset pins each modelled register reads (UG479 Table 2-1)
REG_PINS = {"AREG": ("CEA1", "CEA2", "RSTA"), "BREG": ("CEB1", "CEB2", "RSTB"),
            "CREG": ("CEC", "RSTC"), "MREG": ("CEM", "RSTM"), "PREG": ("CEP", "RSTP")}


def reg_config(regs):
    """regs: {name: int} for REGS + REGS_REFUSED (missing = 0).  -> (rp, pins,
    why): rp the register parameters prims.v takes (REGS), pins the CLK/CE/RST
    pins the model reads (empty when every register is off), why refusals."""
    why = []
    rp = {k: int(regs.get(k, 0) or 0) for k in REGS}
    for k in REGS_REFUSED:
        if int(regs.get(k, 0) or 0):
            why.append("%s=%s (not modelled)" % (k, regs[k]))
    for X in "AB":
        r, c = rp[X + "REG"], rp[X + "CASCREG"]
        ok = {0: (0,), 1: (1,), 2: (1, 2)}.get(r, ())
        if c not in ok:
            why.append("%sREG=%d with %sCASCREG=%d (UG479: AREG 0/1/2 takes ACASCREG 0 / 1 / 1-or-2)"
                       % (X, r, X, c))
    for k in ("CREG", "MREG", "PREG"):
        if rp[k] not in (0, 1):
            why.append("%s=%d" % (k, rp[k]))
    pins = []
    if any(rp[k] for k in ("AREG", "BREG", "CREG", "MREG", "PREG")):
        pins.append("CLK")
        for k, ps in sorted(REG_PINS.items()):
            if rp[k]:
                pins.extend(ps)
    return rp, pins, why


def registered(p):
    return any(p.get(k, 0) for k in REGS)


def config(opmode, alumode, inmode, carryinsel, carryin, regs=None):
    """-> (params, why).  params: XMUX YMUX ZMUX ALUMODE AGATE CIN, plus the
    sets of operand groups the function reads ('A30' all of A, 'A25' A[24:0],
    'B', 'C', 'PCIN').  why: refusal reasons, empty when modelled.  regs: the
    register parameters (reg_config()'s rp); None = every register off, the
    combinational decision exactly as before S7."""
    why = []
    rg = dict.fromkeys(REGS, 0)
    rg.update(regs or {})
    X, Y, Z = opmode & 3, (opmode >> 2) & 3, opmode >> 4
    agate = (inmode >> 1) & 1
    logic = bool(alumode & 0b1100)
    if carryinsel != 0:
        why.append("CARRYINSEL=%s (modelled: 000, CARRYIN)" % format(carryinsel, "03b"))
    # INMODE[0] (A1) / INMODE[4] (B1): modelled once that side has a register
    # (an A1/B1 to select); the pre-adder bits [2]/[3] never are
    bad_in = 0b01100 | (0b00001 if not rg["AREG"] else 0) | (0b10000 if not rg["BREG"] else 0)
    if not agate and inmode & bad_in:
        why.append("INMODE=%s with A not gated: A1/B1 select or pre-adder (AREG=%d BREG=%d, USE_DPORT=FALSE) "
                   "not modelled" % (format(inmode, "05b"), rg["AREG"], rg["BREG"])
                   if registered(rg) else
                   "INMODE=%s with A not gated: A1/B1 select or pre-adder (AREG=BREG=0, USE_DPORT=FALSE) "
                   "not modelled" % format(inmode, "05b"))
    preg = rg["PREG"]
    if X == 2 and not preg:
        why.append("OPMODE X=P with PREG=0 (combinational loop)")
    if Z == 4 and preg:
        why.append("OPMODE Z=100 (P, MACC extend) not modelled")
    if (X == 1) != (Y == 1):
        why.append("OPMODE X/Y=%s: M must be on X and Y together" % format(opmode & 15, "04b"))
    if Z == 7:
        why.append("OPMODE Z=111 (illegal)")
    if alumode & 0b1100 == 0b1000:
        why.append("ALUMODE=%s (not in UG479's tables)" % format(alumode, "04b"))
    if logic and X == 1 and not agate:
        why.append("ALUMODE=%s logic mode reading the multiplier (partial products not modelled)"
                   % format(alumode, "04b"))
    if logic and Y == 3:
        why.append("ALUMODE=%s logic mode with Y=C (UG479: Y must be 0 or all ones)" % format(alumode, "04b"))
    if logic and carryin:
        why.append("CARRYIN=1 in logic mode ALUMODE=%s" % format(alumode, "04b"))
    munk = int(logic and X == 1 and bool(agate))
    zmux = Z
    if preg and Z in (2, 6):
        pass                  # the P register, fed back (prims.v g_reg)
    elif munk and Z in (2, 4, 6):
        zmux = 0              # every output bit is x whatever Z is
    elif preg and Z == 4:
        pass                  # refused above
    elif Z in (2, 4, 6):
        # P fed back with PREG=0: model only if the output cannot depend on Z
        xc = {0: 0}.get(X)
        yc = {0: 0, 2: MASK}.get(Y)
        if xc is None or yc is None or not logic or \
                alu(xc, yc, 0, alumode, carryin) != alu(xc, yc, MASK, alumode, carryin):
            why.append("OPMODE Z=%s (P) with PREG=0: output depends on the fed-back P"
                       % format(Z, "03b"))
        else:
            zmux = 0          # exact: the output is the same for every Z
    reads = set(["B"])
    reads.add("A30" if X == 3 else "A25")
    if Y == 3 or zmux == 3:
        reads.add("C")
    if zmux in (1, 5):
        reads.add("PCIN")
    p = {"XMUX": X, "YMUX": Y, "ZMUX": zmux, "ALUMODE": alumode, "AGATE": agate,
         "CIN": carryin, "MUNK": munk, "reads": reads}
    if registered(rg):
        p.update(rg)
        p["ASEL1"] = int(bool(rg["AREG"] and not agate and inmode & 1))
        p["BSEL1"] = int(bool(rg["BREG"] and not agate and (inmode >> 4) & 1))
    return p, why


def is_default(p):
    return all(p[k] == v for k, v in DEFAULT.items()) and p["ZMUX"] in (0, 1, 5) \
        and not registered(p)


# the register parameters prims.v takes, in the order gen.py writes them
REG_PARAMS = REGS + ("ASEL1", "BSEL1")
