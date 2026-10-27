"""verify/arb_fork.py (rule J) on a hand-built one-arbiter routed JSON + SDF:
it passes balanced A0 branches, fails a late A0 at an ack C-element, and
reports an arbiter it cannot resolve as a gap rather than a pass.  Run with
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q cells/verify/test_arb_fork.py"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
import arb_fork  # noqa: E402

A = "u.arb"
# bits: 1 r1, 2 r2, 3 q, 4 rst, 5 A0, 6 g1, 7 g2, 8 A1, 9 A2
RST_SINKS = 6        # rst reaches more cells than A0, which is how it is told apart


def lut(bel, ins, outs):
    conns, dirs = {}, {}
    for p, b in ins.items():
        conns[p], dirs[p] = [b], "input"
    for p, b in outs.items():
        conns[p], dirs[p] = [b], "output"
    return {"type": "SLICE_LUTX", "connections": conns, "port_directions": dirs,
            "attributes": {"NEXTPNR_BEL": bel}}


def design(a0_to_ua2=400, drop_ua1=False):
    cells = {
        A + ".ustate$LUT6": lut("SLICE_X1Y1/A6LUT", {"A1": 1, "A2": 2, "A3": 3, "A4": 4, "A5": 5}, {"O6": 3}),
        A + ".ugrant$LUT5": lut("SLICE_X1Y1/B5LUT", {"A1": 1, "A2": 2, "A3": 3}, {"O5": 6}),
        A + ".ugrant$LUT6": lut("SLICE_X1Y1/B6LUT", {"A1": 1, "A2": 2, "A3": 3}, {"O6": 7}),
        A + ".ua1.u": lut("SLICE_X1Y1/C6LUT", {"A1": 6, "A2": 5, "A3": 4, "A4": 8}, {"O6": 8}),
        A + ".ua2.u": lut("SLICE_X1Y1/D6LUT", {"A1": 7, "A2": 5, "A3": 4, "A4": 9}, {"O6": 9}),
        "srv": lut("SLICE_X9Y9/A6LUT", {"A1": 8}, {"O6": 5}),
        "por": lut("SLICE_X9Y8/A6LUT", {}, {"O6": 4}),
        "c1": lut("SLICE_X9Y7/A6LUT", {}, {"O6": 1}),
        "c2": lut("SLICE_X9Y6/A6LUT", {}, {"O6": 2}),
    }
    for i in range(RST_SINKS):
        cells[f"other{i}"] = lut(f"SLICE_X8Y{i}/A6LUT", {"A1": 4}, {"O6": 100 + i})
    if drop_ua1:
        del cells[A + ".ua1.u"]
    ic = {("srv/O6", A + ".ustate$LUT6/A5"): 400, ("srv/O6", A + ".ua1.u/A2"): 400,
          ("srv/O6", A + ".ua2.u/A2"): a0_to_ua2,
          (A + ".ustate$LUT6/O6", A + ".ugrant$LUT5/A3"): 200,
          (A + ".ustate$LUT6/O6", A + ".ugrant$LUT6/A3"): 200,
          (A + ".ugrant$LUT5/O5", A + ".ua1.u/A1"): 200,
          (A + ".ugrant$LUT6/O6", A + ".ua2.u/A1"): 200}
    io = {(A + ".ustate$LUT6", "A5", "O6"): 124, (A + ".ugrant$LUT5", "A3", "O5"): 124,
          (A + ".ugrant$LUT6", "A3", "O6"): 124, (A + ".ua1.u", "A1", "O6"): 124,
          (A + ".ua1.u", "A2", "O6"): 124, (A + ".ua2.u", "A1", "O6"): 124,
          (A + ".ua2.u", "A2", "O6"): 124}
    sdf = ["(DELAYFILE"]
    for (s, d), ps in ic.items():
        sdf.append(f"  (INTERCONNECT {s} {d} ({ps}:{ps}:{ps}) ({ps}:{ps}:{ps}))")
    by = {}
    for (inst, a, z), ps in io.items():
        by.setdefault(inst, []).append((a, z, ps))
    for inst, arcs in by.items():
        sdf.append(f"  (CELL (CELLTYPE \"X\") (INSTANCE {inst}) (DELAY (ABSOLUTE")
        for a, z, ps in arcs:
            sdf.append(f"      (IOPATH {a} {z} ({ps}:{ps}:{ps}) ({ps}:{ps}:{ps}))")
        sdf.append("  ))))")
    sdf.append(")")
    return {"modules": {"top": {"attributes": {"top": 1}, "cells": cells, "netnames": {}}}}, "\n".join(sdf)


def run(tmp_path, **kw):
    j, s = design(**kw)
    (tmp_path / "d_routed.json").write_text(json.dumps(j))
    (tmp_path / "d.sdf").write_text(s)
    return arb_fork.main([str(tmp_path / "d.sdf")])


def test_balanced_branches_pass(tmp_path, capsys):
    assert run(tmp_path) == 0
    assert "VIOLATED" not in capsys.readouterr().out


def test_late_a0_at_an_ack_fails(tmp_path, capsys):
    # early = 400+124+200+124+200+124 = 1172; late must stay under 0.772*1172/1.155 - 124
    assert run(tmp_path, a0_to_ua2=900) == 1
    out = capsys.readouterr().out
    assert "VIOLATED" in out and "client 2" in out


def test_unresolved_arbiter_is_a_gap(tmp_path, capsys):
    assert run(tmp_path, drop_ua1=True) == 2
    assert "NOT RESOLVED" in capsys.readouterr().out
