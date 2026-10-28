"""DSP48E1 combinational configurations that prims.v's DSP48E1_DSP48E1 models.

One decision, shared by gen.py (routed JSON or bits-built JSON) and
fid/fasm2net.py (the bits): given the decoded control words of a DSP48E1
with EVERY pipeline register off, either the model parameters that simulate
it, or the reasons it is refused.  A refusal is better than a mis-simulation.

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
reading the multiplier unless M is identically zero (A gated: ASSUMPTION that
both partial products are then zero); ALUMODE 10xx (not in UG479's tables);
CARRYINSEL other than 000; CARRYIN=1 in a logic mode; Z=111.
"""

MASK = (1 << 48) - 1
DEFAULT = {"XMUX": 1, "YMUX": 1, "ALUMODE": 0, "AGATE": 0, "CIN": 0}


def alu(x, y, z, alumode, cin):
    """The ALU as prims.v computes it (48-bit words, unsigned)."""
    zi = (~z & MASK) if alumode & 1 else z
    s = x ^ y ^ zi
    c = (x & y) | (x & zi) | (y & zi)
    smux = c if alumode & 8 else s
    cmux = 0 if alumode & 4 else c
    r = (smux + (cmux << 1) + cin) & MASK
    return (~r & MASK) if alumode & 2 else r


def config(opmode, alumode, inmode, carryinsel, carryin):
    """-> (params, why).  params: XMUX YMUX ZMUX ALUMODE AGATE CIN, plus the
    sets of operand groups the function reads ('A30' all of A, 'A25' A[24:0],
    'B', 'C', 'PCIN').  why: refusal reasons, empty when modelled."""
    why = []
    X, Y, Z = opmode & 3, (opmode >> 2) & 3, opmode >> 4
    agate = (inmode >> 1) & 1
    logic = bool(alumode & 0b1100)
    if carryinsel != 0:
        why.append("CARRYINSEL=%s (modelled: 000, CARRYIN)" % format(carryinsel, "03b"))
    if not agate and inmode & 0b11101:
        why.append("INMODE=%s with A not gated: A1/B1 select or pre-adder (AREG=BREG=0, USE_DPORT=FALSE) "
                   "not modelled" % format(inmode, "05b"))
    if X == 2:
        why.append("OPMODE X=P with PREG=0 (combinational loop)")
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
    zmux = Z
    if Z in (2, 4, 6):
        # P fed back with PREG=0: model only if the output cannot depend on Z
        xc = {0: 0}.get(X, 0 if (X == 1 and agate) else None)
        yc = {0: 0, 2: MASK}.get(Y, 0 if (Y == 1 and agate) else None)
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
         "CIN": carryin, "reads": reads}
    return p, why


def is_default(p):
    return all(p[k] == v for k, v in DEFAULT.items()) and p["ZMUX"] in (0, 1, 5)
