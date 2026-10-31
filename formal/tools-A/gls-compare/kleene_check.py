#!/usr/bin/env python3
"""kleene_check.py -- does the GLS's ?: mux tree equal Lean's Kleene LUT eval?

Lean reference (formal/lean/Formal/Core/Lut.lean): `Lut.keval` = `kevalT`
(A1 at the root), proved equal to the order-free spec `Lut.kevalSpec`
(`keval_eq_kevalSpec`): binary b iff every Boolean completion of the X pins
addresses an INIT bit equal to b, else X.  LutTree.lean's `kmux`: select X ->
data if equal else X.  Usage: python3 -I kleene_check.py PRIMS_V
"""
import itertools, os, random, subprocess, sys, tempfile

LIB = {  # from formal/lean/Formal/Core/Lut.lean (namespace Init)
    "bd_c2": 0x00E8_00E8_00E8_00E8, "bd_c2_set": 0xFFE8_FFE8_FFE8_FFE8,
    "bd_c2n": 0x00B2_00B2_00B2_00B2, "bd_c2n_set": 0xFFB2_FFB2_FFB2_FFB2,
    "bd_c3": 0x0000_FE80_0000_FE80, "bd_c4": 0x0000_0000_FFFE_8000,
    "bd_c2_norst": 0xE8E8_E8E8_E8E8_E8E8, "bd_c3_norst": 0xFE80_FE80_FE80_FE80,
    "arb_grant": 0x0C0C_0C0C_A0A0_A0A0, "arb_state": 0xFFF0_FFB2_ACAC_ACAC,
    "latch_pair": 0xFF33_CC00_B8B8_B8B8, "latch_odd": 0xB8B8_B8B8_B8B8_B8B8,
    "latch_rst0": 0x00B8_00B8_00B8_00B8, "latch_rst1": 0xFFB8_FFB8_FFB8_FFB8,
    "datamux_pair": 0xFFAA_5500_E4E4_E4E4, "zero": 0, "ones": (1 << 64) - 1,
    "xor6": int("".join("1" if bin(i).count("1") % 2 else "0" for i in reversed(range(64))), 2),
}

def kspec(init, vec):  # vec: list of '0','1','x' for A1..Ak
    opts = [[0, 1] if c == "x" else [int(c)] for c in vec]
    vals = {(init >> sum(b << i for i, b in enumerate(w))) & 1 for w in itertools.product(*opts)}
    return "x" if len(vals) == 2 else str(vals.pop())

def kmux(d0, d1, s):
    if s == "0": return d0
    if s == "1": return d1
    return d0 if d0 == d1 else "x"

def main():
    prims = sys.argv[1]
    rng = random.Random(11)
    inits = dict(LIB)
    for k in range(12):
        inits["rand%d" % k] = rng.getrandbits(64)
    here = os.path.dirname(os.path.abspath(__file__))
    bad = 0; total = 0
    with tempfile.TemporaryDirectory() as wd:
        for name, init in inits.items():
            vvp = os.path.join(wd, "k.vvp")
            subprocess.run(["iverilog", "-gspecify", "-Ptb_kleene.INIT=64'h%016X" % init, "-o", vvp,
                            os.path.join(here, "tb_kleene.v"), prims], check=True)
            out = subprocess.run(["vvp", "-n", vvp], check=True, capture_output=True, text=True).stdout
            nb = 0
            for l in out.splitlines():
                t = l.split()
                if t[0] == "V":
                    vec = list(t[1]); o6, o5 = t[2], t[3]
                    e6 = kspec(init, vec)
                    e5 = kspec(init & 0xFFFF_FFFF, vec[:5])
                    total += 2
                    if o6 != e6: nb += 1; print("MISMATCH %s O6 %s gls=%s lean=%s" % (name, t[1], o6, e6))
                    if o5 != e5: nb += 1; print("MISMATCH %s O5 %s gls=%s lean=%s" % (name, t[1], o5, e5))
                elif t[0] == "M" and name == "zero":
                    total += 1
                    if t[4] != kmux(t[1], t[2], t[3]):
                        nb += 1; print("MISMATCH SELMUX2_1 %s" % l)
            bad += nb
            print("%-13s INIT=64'h%016X  mismatches %d" % (name, init, nb))
    print("TOTAL: %d comparisons, %d mismatches" % (total, bad))

if __name__ == "__main__":
    main()
