"""verify/fasm_audit.py, and the GLS translator's copy of the same LUT decode.

Regression tests for the August 2026 bitstream bugs (patches/README.md), on
synthetic routed netlists, so they need no toolchain.  Each bug gets a pass
case (what the patched writer writes) and a fail case (what the unpatched one
wrote), and the fail case is computed by the same emulation
verify/fasm/check.sh runs against a real route.
"""
import json
import os
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "gls"))
import fasm_audit as fa  # noqa: E402
import gen  # noqa: E402


@pytest.fixture
def db(tmp_path):
    """A two-tile device: one CLBLM (SLICEM X0, SLICEL X1) and one DSP_L."""
    (tmp_path / "xc7z010").mkdir()
    grid = {
        "CLBLM_R_X1Y1": {"type": "CLBLM_R",
                         "sites": {"SLICE_X2Y1": "SLICEM", "SLICE_X3Y1": "SLICEL"}},
        "DSP_L_X4Y0": {"type": "DSP_L",
                       "sites": {"DSP48_X0Y0": "DSP48E1", "DSP48_X0Y1": "DSP48E1",
                                 "TIEOFF_X5Y0": "TIEOFF"}},
    }
    (tmp_path / "xc7z010" / "tilegrid.json").write_text(json.dumps(grid))
    segbits = "".join("DSP_L.DSP_0_%s.DSP_%s_L 1_1\n" % (p, n)
                      for p in ("INMODE0", "INMODE1", "OPMODE6", "D0")
                      for n in ("GND", "VCC"))
    (tmp_path / "segbits_dsp_l.db").write_text(segbits)
    return str(tmp_path)


def lut(bel, init, ports, typ="LUT4"):
    attrs = {"NEXTPNR_BEL": bel, "X_ORIG_TYPE": typ}
    attrs.update({"X_ORIG_PORT_A%d" % k: v for k, v in ports.items()})
    return {"type": "SLICE_LUTX", "attributes": attrs, "parameters": {"INIT": init},
            "connections": {}, "port_directions": {}}


# A LUT4 whose net on I0 is also on I2, so the packer put both on A1 and wrote
# the attribute run together -- the form gcd_hw's 131 LUTs had.
RUN_TOGETHER = lut("SLICE_X3Y1/B6LUT", format(0x6A5C, "016b"),
                   {1: "I2I0 ", 2: "I1", 3: "I3"})
SPACED = lut("SLICE_X2Y1/A6LUT", format(0xCA, "08b"), {1: "I0 I2", 4: "I1"}, "LUT3")


def write(tmp_path, cells, fasm_lines, synth=None):
    r = tmp_path / "routed.json"
    r.write_text(json.dumps({"modules": {"top": {"attributes": {"top": "1"}, "cells": cells}}}))
    f = tmp_path / "x.fasm"
    f.write_text("\n".join(fasm_lines) + "\n")
    s = None
    if synth is not None:
        s = tmp_path / "synth.json"
        s.write_text(json.dumps({"modules": {"t": {"attributes": {"top": "1"}, "cells": synth}}}))
    return str(r), str(f), (str(s) if s else None)


def lut_line(prefix, bits):
    return "%s.INIT[63:0] = 64'b%s" % (prefix, format(bits, "064b"))


# ----------------------------------------------------------------- LUT INIT

def test_run_together_pin_decodes_both_inputs():
    # A1 carries I0 and I2: setting A1 must set address bits 0 and 2.
    bits = fa.expected_lut_bits(RUN_TOGETHER, None)
    assert (bits >> 0b000001) & 1 == (0x6A5C >> 0b0101) & 1
    for j in range(64):
        a1, a2, a3 = j & 1, (j >> 1) & 1, (j >> 2) & 1
        log = a1 | (a2 << 1) | (a1 << 2) | (a3 << 3)
        assert (bits >> j) & 1 == (0x6A5C >> log) & 1


def test_unpatched_parser_reads_run_together_as_I0():
    assert fa.unpatched_lut_names({"X_ORIG_PORT_A1": "I2I0 "}, 0) == [0, 0]
    assert fa.unpatched_lut_names({"X_ORIG_PORT_A1": "I0 I3"}, 0) == [0, 3]
    assert fa.expected_lut_bits(RUN_TOGETHER, None, fa.unpatched_lut_names) != \
        fa.expected_lut_bits(RUN_TOGETHER, None)
    # the space-separated form was always decoded right
    assert fa.expected_lut_bits(SPACED, None, fa.unpatched_lut_names) == \
        fa.expected_lut_bits(SPACED, None)


def test_audit_passes_patched_and_fails_unpatched_lut(tmp_path, db):
    cells = {"a": RUN_TOGETHER, "b": SPACED}
    good = [lut_line("CLBLM_R_X1Y1.SLICEL_X1.BLUT", fa.expected_lut_bits(RUN_TOGETHER, None)),
            lut_line("CLBLM_R_X1Y1.SLICEM_X0.ALUT", fa.expected_lut_bits(SPACED, None))]
    r, f, _ = write(tmp_path, cells, good)
    rc, st = fa.audit(r, f, db=db, out=open(os.devnull, "w"))
    assert rc == 0 and st["runtogether"] == 1 and st["lut_sites"] == 2
    bad = str(tmp_path / "bad.fasm")
    assert fa.write_unpatched("pinmap", r, f, bad, db) == 1
    rc, st = fa.audit(r, bad, db=db, out=open(os.devnull, "w"))
    assert rc == 1 and st["bad"] == 1


def test_fractured_pair_splits_the_table(tmp_path, db):
    l6 = lut("SLICE_X2Y1/C6LUT", format(0x96, "08b"), {1: "I0", 2: "I1", 3: "I2"}, "LUT3")
    l5 = lut("SLICE_X2Y1/C5LUT", format(0x8, "04b"), {1: "I1", 2: "I0"}, "LUT2")
    bits = fa.expected_lut_bits(l6, l5)
    lo, hi = bits & 0xFFFFFFFF, bits >> 32
    for j in range(32):
        assert (lo >> j) & 1 == (0x8 >> (((j >> 1) & 1) | ((j & 1) << 1))) & 1
        assert (hi >> j) & 1 == (0x96 >> (j & 7)) & 1
    r, f, _ = write(tmp_path, {"x": l6, "y": l5},
                    [lut_line("CLBLM_R_X1Y1.SLICEM_X0.CLUT", bits)])
    assert fa.audit(r, f, db=db, out=open(os.devnull, "w"))[0] == 0
    # the halves swapped is a different bitstream, and must be caught
    r, f, _ = write(tmp_path, {"x": l6, "y": l5},
                    [lut_line("CLBLM_R_X1Y1.SLICEM_X0.CLUT", (lo << 32) | hi)])
    assert fa.audit(r, f, db=db, out=open(os.devnull, "w"))[0] == 1


# ---------------------------------------- gls/gen.py must decode the same way

def gen_table(cell, port):
    return gen.expand_lut_init(cell["parameters"]["INIT"], cell["attributes"], port)


def test_gls_translator_agrees_with_the_bitstream():
    """gen.py had the same whitespace-split bug independently, which is why
    GLS called gcd's comparator wrong while the die got it right."""
    for c in (RUN_TOGETHER, SPACED):
        assert gen_table(c, "O6") == fa.expected_lut_bits(c, None)


def test_gls_translator_with_the_august_parser_disagrees(monkeypatch):
    class Split:
        @staticmethod
        def findall(s):
            return s.split()
    monkeypatch.setattr(gen, "RE_ORIG_PORT", Split())
    assert gen_table(RUN_TOGETHER, "O6") != fa.expected_lut_bits(RUN_TOGETHER, None)


# -------------------------------------------------------------------- DSPs

def dsp(areg, acasc, vcc_pins="", gnd_pins="", inv=()):
    params = {"AREG": format(areg, "032b"), "ACASCREG": format(acasc, "032b"),
              "BREG": format(0, "032b"), "BCASCREG": format(0, "032b")}
    params.update({k: "1" for k in inv})
    return {"type": "DSP48E1_DSP48E1", "parameters": params, "connections": {},
            "attributes": {"NEXTPNR_BEL": "DSP48_X0Y0/DSP48E1",
                           "DSP_VCC_PINS": vcc_pins, "DSP_GND_PINS": gnd_pins}}


def synth_dsp(inmode="00000", opmode="0000101", d0="0"):
    # yosys JSON: connection bit lists are LSB first
    return {"type": "DSP48E1", "parameters": {},
            "connections": {"INMODE": list(reversed(inmode)), "OPMODE": list(reversed(opmode)),
                            "D": [d0] + ["0"] * 24}}


Z = "DSP_L_X4Y0.DSP48.DSP_0.Z%sREG_2_%sCASCREG_1"
CONST_OK = ["DSP_L_X4Y0.DSP_0_INMODE0.DSP_GND_L", "DSP_L_X4Y0.DSP_0_INMODE1.DSP_GND_L",
            "DSP_L_X4Y0.DSP_0_OPMODE6.DSP_GND_L", "DSP_L_X4Y0.DSP_0_D0.DSP_GND_L"]


@pytest.mark.parametrize("areg,acasc,bit", [(0, 0, True), (1, 1, True), (2, 1, False), (2, 2, True)])
def test_zareg_is_the_conjunction(tmp_path, db, areg, acasc, bit):
    feats = ([Z % ("A", "A")] if bit else []) + [Z % ("B", "B")] + CONST_OK
    r, f, s = write(tmp_path, {"m": dsp(areg, acasc)}, feats, {"m": synth_dsp()})
    assert fa.audit(r, f, s, db=db, out=open(os.devnull, "w"))[0] == 0
    bad = str(tmp_path / "bad.fasm")
    fa.write_unpatched("areg", r, f, bad, db)
    # unpatched: bit iff ACASCREG == 0, which is right only for (0,0) and (2,1)
    caught = fa.audit(r, bad, s, db=db, out=open(os.devnull, "w"))[0] == 1
    assert caught == ((areg, acasc) in ((1, 1), (2, 2)))


def test_const_pins_missing_or_uninverted_are_caught(tmp_path, db):
    # nextpnr ties the 0s to VCC with the per-bit site inversion set, as it
    # does for a plain inferred multiply; the tile bit must still say GND.
    routed = {"m": dsp(1, 1, vcc_pins="INMODE0 INMODE1 OPMODE6", gnd_pins="D0",
                       inv=("IS_INMODE[0]_INVERTED", "IS_INMODE[1]_INVERTED",
                            "IS_OPMODE[6]_INVERTED"))}
    feats = [Z % ("A", "A"), Z % ("B", "B")] + CONST_OK
    r, f, s = write(tmp_path, routed, feats, {"m": synth_dsp()})
    rc, st = fa.audit(r, f, s, db=db, out=open(os.devnull, "w"))
    assert rc == 0 and st["const"] == 4
    for kind, n in (("constpins-packer", 3), ("constpins-inv", 3)):
        bad = str(tmp_path / ("%s.fasm" % kind))
        fa.write_unpatched(kind, r, f, bad, db)
        rc, st = fa.audit(r, bad, s, db=db, out=open(os.devnull, "w"))
        assert rc == 1 and st["bad"] == n, kind


def test_const_pin_value_comes_from_synthesis_not_the_packer(tmp_path, db):
    # INMODE[1] = 1 in the yosys netlist: the tile bit must be VCC, whatever
    # the packer's attributes say.
    feats = [Z % ("A", "A"), Z % ("B", "B")] + CONST_OK
    r, f, s = write(tmp_path, {"m": dsp(1, 1)}, feats, {"m": synth_dsp(inmode="00010")})
    rc, st = fa.audit(r, f, s, db=db, out=open(os.devnull, "w"))
    assert rc == 1 and st["bad"] == 1


# ------------------------------------------- hierarchical synthesis netlists

def hier(tmp_path, cells_in_sub):
    mods = {
        "top_m": {"attributes": {"top": "1"}, "cells": {"uut": {"type": "sub_m"}}},
        "sub_m": {"attributes": {}, "cells": dict(cells_in_sub, u2={"type": "leaf_m"})},
        "leaf_m": {"attributes": {}, "cells": {"x.y": {"type": "DSP48E1"}}},
        "DSP48E1": {"attributes": {"blackbox": "1"}, "cells": {}},
    }
    p = tmp_path / "h.json"
    p.write_text(json.dumps({"modules": mods}))
    return fa.SynthCells(str(p))


def test_flattened_name_walks_the_hierarchy(tmp_path):
    sc = hier(tmp_path, {"$mul$a.v:1$2.g.mul": {"type": "DSP48E1", "tag": 1}})
    assert sc.get("uut.$mul$a.v:1$2.g.mul")["tag"] == 1
    assert sc.get("uut.u2.x.y")["type"] == "DSP48E1"   # blackbox type is a leaf


def test_unresolvable_or_ambiguous_name_is_an_error(tmp_path):
    sc = hier(tmp_path, {"m": {"type": "DSP48E1"}})
    with pytest.raises(LookupError):
        sc.get("uut.nope")
    with pytest.raises(LookupError):
        sc.get("m")                                       # exists only below the top
    # "u2.x.y" both as a cell of sub_m and as instance u2's cell x.y
    sc = hier(tmp_path, {"u2.x.y": {"type": "DSP48E1"}})
    with pytest.raises(LookupError):
        sc.get("uut.u2.x.y")
