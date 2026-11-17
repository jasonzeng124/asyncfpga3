#!/usr/bin/env python3
"""margin/dsp/dspmodel.py (shard C, UNTRUSTED): the combinational DSP48E1 datapath (every register off), in Python.

The reference for simx.cpp's dsp48 gate (the C++ is a transcription of dsp_p() below; selftest() compares the two
through simx --dsptest: `dspmodel.py PATH/TO/simx`) and for decode_dsp.py's numeric check. Semantics: yosys's cells_sim.v DSP48E1 model
(share/yosys/xilinx/cells_sim.v of the toolchain: the model research's GLS simulates), specialised to
AREG = BREG = ACASCREG = BCASCREG = CREG = DREG = ADREG = MREG = PREG = 0, OPMODEREG = ALUMODEREG = INMODEREG =
CARRYINREG = CARRYINSELREG = 0, USE_DPORT = FALSE, USE_SIMD = ONE48 (UG479 ch. 2):

  A_MULT = INMODE[1] ? 0 : A[24:0] (signed; INMODE[0] / INMODE[4] pick A1/A2, B1/B2, which are equal with AREG = BREG = 0;
           INMODE[3:2] act on the D pre-adder only, bypassed with USE_DPORT = FALSE)
  M      = A_MULT * B (25 x 18 signed -> 43 bits, sign-extended to 48)
  X      = OPMODE[1:0]: 00 -> 0, 01 -> M (Y must be 01), 11 -> {A, B};      10 (P feedback) REFUSED (PREG = 0: a loop)
  Y      = OPMODE[3:2]: 00 -> 0, 01 -> 0 (M is carried whole on X), 10 -> all ones, 11 -> C
  Z      = OPMODE[6:4]: 000 -> 0, 001 -> PCIN, 011 -> C, 101 -> PCIN >>> 17 (sign-extended, as cells_sim's $signed);
           010 / 100 / 110 (P feedback) and 111 REFUSED
  cin    = CARRYINSEL 000 -> CARRYIN; any other CARRYINSEL REFUSED; gated to 0 when ALUMODE[3] | ALUMODE[2]
  ALU    = cells_sim's: Z' = ALUMODE[0] ? ~Z : Z; s = X ^ Y ^ Z', c = maj(X, Y, Z'); s' = ALUMODE[3] ? c : s;
           c' = ALUMODE[2] ? 0 : c; sum = ({c', cin} + s') mod 2^48; P = ALUMODE[1] ? ~sum : sum.  PCOUT = P.
"""
import sys
M48 = (1 << 48) - 1


def sext(v, w):
    v &= (1 << w) - 1
    return v - (1 << w) if v >> (w - 1) else v


class Refused(Exception):
    pass


def check_cfg(opmode, alumode, inmode, carryinsel):
    x, y, z = opmode & 3, (opmode >> 2) & 3, (opmode >> 4) & 7
    if x == 2:
        raise Refused("OPMODE[1:0] = 10 (X = P) with PREG = 0")
    if (x == 1) != (y == 1):
        raise Refused("OPMODE[1:0] / [3:2] = %d / %d: M must be on both X and Y" % (x, y))
    if z in (2, 4, 6, 7):
        raise Refused("OPMODE[6:4] = %s (P feedback or reserved) with PREG = 0" % format(z, "03b"))
    if carryinsel != 0:
        raise Refused("CARRYINSEL = %s (only 000 = CARRYIN modelled)" % format(carryinsel, "03b"))
    if alumode >> 4 or inmode >> 5 or opmode >> 7:
        raise Refused("control value out of range")


def used_ports(opmode, alumode, inmode, carryinsel):
    """The data ports the function reads (the rest cannot change P)."""
    x, y, z = opmode & 3, (opmode >> 2) & 3, (opmode >> 4) & 7
    u = set()
    if x == 1:
        u |= {"B"} | (set() if inmode & 2 else {"A"})
    if x == 3:
        u |= {"A", "B"}
    if y == 3 or z == 3:
        u.add("C")
    if z in (1, 5):
        u.add("PCIN")
    if carryinsel == 0 and not (alumode & 12):
        u.add("CARRYIN")
    return u


def dsp_p(opmode, alumode, inmode, carryinsel, A, B, C, PCIN, CARRYIN):
    """P (48 bits) of a combinational DSP48E1; A 30 bits (A_INPUT's choice), B 18 bits (B_INPUT's), C / PCIN 48."""
    check_cfg(opmode, alumode, inmode, carryinsel)
    x, y, z = opmode & 3, (opmode >> 2) & 3, (opmode >> 4) & 7
    am = 0 if inmode & 2 else sext(A, 25)
    m = (am * sext(B, 18)) & M48
    X = {0: 0, 1: m, 3: ((A & ((1 << 30) - 1)) << 18 | (B & ((1 << 18) - 1))) & M48}[x]
    Y = {0: 0, 1: 0, 2: M48, 3: C & M48}[y]
    Z = {0: 0, 1: PCIN & M48, 3: C & M48, 5: sext((PCIN & M48) >> 17, 31) & M48}[z]
    cin = 0 if alumode & 12 else (CARRYIN & 1)
    Zi = (~Z & M48) if alumode & 1 else Z
    s = X ^ Y ^ Zi
    c = (X & Y) | (X & Zi) | (Y & Zi)
    s2 = c if alumode & 8 else s
    c2 = 0 if alumode & 4 else c
    tot = (((c2 << 1) | cin) + s2) & M48
    return (~tot & M48) if alumode & 2 else tot


if __name__ == "__main__":
    import random
    r = random.Random(1)
    for _ in range(20000):   # unsigned 17 x 17 products on X = Y = M, and the PCIN >>> 17 add
        a, b, pc = r.getrandbits(17), r.getrandbits(17), r.getrandbits(48)
        assert dsp_p(0b0000101, 0, 0, 0, a, b, 0, 0, 0) == a * b
        assert dsp_p(0b1010101, 0, 0, 0, a, b, 0, pc, 0) == (a * b + sext(pc >> 17, 31)) & M48
        assert dsp_p(0b0000101, 0b0011, 0, 0, a, b, 0, 0, 0) == (-(a * b)) & M48   # Z - (X + Y + cin), Z = 0
    print("dspmodel: self-check ok")
    if len(sys.argv) > 1:   # dspmodel.py SIMX: simx.cpp's dsp48_p against dsp_p on random supported configurations
        import subprocess
        cases = []
        while len(cases) < 50000:
            opm, alu, inm = r.getrandbits(7), r.getrandbits(4), r.getrandbits(5)
            try:
                check_cfg(opm, alu, inm, 0)
            except Refused:
                continue
            cases.append((opm, alu, inm, 0, r.getrandbits(30), r.getrandbits(18), r.getrandbits(48), r.getrandbits(48), r.getrandbits(1)))
        out = subprocess.run([sys.argv[1], "--dsptest"], input="".join("%d %d %d %d %x %x %x %x %d\n" % c for c in cases),
                             capture_output=True, text=True, check=True).stdout.split()
        bad = sum(1 for c, o in zip(cases, out) if int(o, 16) != dsp_p(*c))
        print("dspmodel: simx --dsptest: %d cases (%d configurations), %d mismatches" % (len(out), len({c[:3] for c in cases}), bad + abs(len(out) - len(cases))))
        sys.exit(1 if bad or len(out) != len(cases) else 0)
