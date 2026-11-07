"""verify/cdc_fsm.py on hand-built gate-level netlists.

The August bench hang, in miniature: a black-box kernel output async-sets a
flop (the edge latch), and the state register reads that latch -- directly
(the bug), through one flop (still a bug), or through two (the fix).
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cdc_fsm  # noqa: E402

CLK, RSTN, KREQ, LATCH, S0, S1, ST, NXT = 2, 3, 10, 11, 12, 13, 14, 15


def netlist(tmp_path, stages, st_reads=None):
    """kernel.o_req -> async-load flop `latched` -> `stages` sync flops -> st."""
    cells = {
        "kern": {"type": "bdc_k", "connections": {"o_req": [KREQ]}},
        "latch": {"type": "$_ALDFF_PP_", "port_directions":
                  {"C": "input", "D": "input", "L": "input", "AD": "input", "Q": "output"},
                  "connections": {"C": [CLK], "D": ["0"], "L": [KREQ], "AD": ["1"], "Q": [LATCH]}},
    }
    src = LATCH
    for i, q in enumerate((S0, S1)[:stages]):
        cells["sync%d" % i] = {"type": "$_DFF_PN0_", "port_directions":
                               {"C": "input", "D": "input", "R": "input", "Q": "output"},
                               "connections": {"C": [CLK], "D": [src], "R": [RSTN], "Q": [q]}}
        src = q
    if st_reads is not None:
        src = st_reads
    cells["next"] = {"type": "$_OR_", "port_directions": {"A": "input", "B": "input", "Y": "output"},
                     "connections": {"A": [src], "B": [ST], "Y": [NXT]}}
    cells["st"] = {"type": "$_DFF_PN0_", "port_directions":
                   {"C": "input", "D": "input", "R": "input", "Q": "output"},
                   "connections": {"C": [CLK], "D": [NXT], "R": [RSTN], "Q": [ST]}}
    mods = {
        "top": {"attributes": {"top": "00000000000000000000000000000001"},
                "ports": {"aclk": {"direction": "input", "bits": [CLK]},
                          "aresetn": {"direction": "input", "bits": [RSTN]}},
                "cells": cells,
                "netnames": {"st": {"bits": [ST], "hide_name": 0},
                             "o_req_latched": {"bits": [LATCH], "hide_name": 0}}},
        "bdc_k": {"attributes": {"blackbox": "1"},
                  "ports": {"o_req": {"direction": "output", "bits": [2]}}, "cells": {}},
    }
    p = tmp_path / "n.json"
    p.write_text(json.dumps({"modules": mods}))
    return str(p)


def test_two_flop_synchroniser_passes(tmp_path):
    found, bad = cdc_fsm.analyse(netlist(tmp_path, 2))
    assert found == 1 and bad == []


def test_august_direct_read_of_the_async_latch_fails(tmp_path):
    found, bad = cdc_fsm.analyse(netlist(tmp_path, 0))
    assert found == 1 and any("async L" in b for b in bad)


def test_one_flop_synchroniser_fails(tmp_path):
    found, bad = cdc_fsm.analyse(netlist(tmp_path, 1))
    assert any("one-flop" in b for b in bad)


def test_raw_kernel_output_fails(tmp_path):
    found, bad = cdc_fsm.analyse(netlist(tmp_path, 2, st_reads=KREQ))
    assert any("bbox" in b for b in bad)


def test_absent_register_is_not_a_pass(tmp_path):
    found, bad = cdc_fsm.analyse(netlist(tmp_path, 2), regs=("nope",))
    assert found == 0
