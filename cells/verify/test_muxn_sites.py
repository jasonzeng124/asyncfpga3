#!/usr/bin/env python3
"""test_muxn_sites.py -- tighten.muxn_decode_sites() on a synthetic routed netlist: a bdc_muxn3 whose three decode LUTs
sel[k] = ctl_req & (s == k) sit on permuted physical pins (as nextpnr places them), and the abstention when a decode
is not one minterm with the request as its only positive literal in sel[0]."""
import json, pathlib, sys, tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.argv = [sys.argv[0], "/nonexistent.sdf"]
import tighten as T                                                     # noqa: E402

P = "top.udut.umux9"
CTL, S0, S1 = 10, 11, 12


def lut(init, phys, outnet):
    """phys: {logical input index: physical pin, ...} with the net on it as (pin, net)."""
    attrs = {"X_ORIG_PORT_%s" % pin: "I%d" % k for k, (pin, _) in phys.items()}
    attrs["X_ORIG_PORT_O6"] = "O"
    conns = {pin: [net] for pin, net in phys.values()}
    conns["O6"] = [outnet]
    dirs = {pin: "input" for pin in conns if pin != "O6"}
    dirs["O6"] = "output"
    return {"type": "SLICE_LUTX", "parameters": {"INIT": init}, "attributes": attrs, "connections": conns,
            "port_directions": dirs}


def netlist(dec0_init="00010000"):
    cells = {}
    # decode LUTs, logical I0 = s0, I1 = s1, I2 = ctl_req; INIT MSB first (row a at position len-1-a)
    cells[P + ".$abc$1"] = lut(dec0_init, {0: ("A2", S0), 1: ("A3", S1), 2: ("A4", CTL)}, 20)      # row 4: ctl & ~s0 & ~s1
    cells[P + ".$abc$2"] = lut("00100000", {0: ("A1", S0), 1: ("A4", S1), 2: ("A3", CTL)}, 21)     # row 5: ctl & s0 & ~s1
    cells[P + ".$abc$3"] = lut("01000000", {0: ("A1", S0), 1: ("A2", S1), 2: ("A5", CTL)}, 22)     # row 6: ctl & ~s0 & s1
    for k in range(3):   # bd_c2 joins: I0 a = in_k_req, I1 b = sel[k], I2 q, I3 rst (b on a different pin each time)
        b_pin = ("A2", "A5", "A1")[k]
        others = [p for p in ("A1", "A2", "A3", "A4", "A5") if p != b_pin]
        phys = {1: (b_pin, 20 + k), 0: (others[0], 30 + k), 2: (others[1], 40 + k), 3: (others[2], 50)}
        cells["%s.uj%d.u" % (P, k)] = lut("0" * 48 + "0000000011101000", phys, 40 + k)
        cells["%s.ua%d.u" % (P, k)] = lut("0" * 48 + "0000000011101000", {0: ("A1", 40 + k), 1: ("A2", 60)}, 70 + k)
    cells[P + ".uor"] = lut("10", {0: ("A5", 80)}, 81)
    return {"modules": {"top": {"cells": cells}}}


def run(nl):
    with tempfile.TemporaryDirectory() as d:
        j = pathlib.Path(d) / "x_routed.json"
        j.write_text(json.dumps(nl))
        return T.muxn_decode_sites(j)


def test_found():
    sites, notes = run(netlist())
    assert notes == [], notes
    got = [(c.rsplit(".", 1)[1], rp.split("/")[1], [s.split("/")[1] for s in sp]) for _, c, rp, sp in sites]
    assert got == [("$abc$1", "A4", ["A2", "A3"]), ("$abc$2", "A3", ["A1", "A4"]), ("$abc$3", "A5", ["A1", "A2"])], got
    assert all(p == P for p, _, _, _ in sites)


def test_abstains():
    sites, notes = run(netlist(dec0_init="01110000"))      # ctl & (~s0 | ~s1): rows 4, 5, 6 -- not one minterm
    assert sites == [] and len(notes) == 1 and "not checked" in notes[0], (sites, notes)


def test_minterm_over_read_pins():
    sites, notes = run(netlist(dec0_init="00110000"))      # ctl & ~s1 (reads no s0): one minterm over what it reads
    assert notes == [] and [s.split("/")[1] for s in sites[0][3]] == ["A3"], (sites, notes)


def test_no_mux_without_acks():
    nl = netlist()
    del nl["modules"]["top"]["cells"][P + ".ua1.u"]         # not emit_muxn's shape: not a bdc_muxnN
    assert run(nl) == ([], [])


if __name__ == "__main__":
    for t in (test_found, test_abstains, test_minterm_over_read_pins, test_no_mux_without_acks):
        t()
        print("ok", t.__name__)
