"""hw/rloc_stamp.py on a hand-built yosys JSON: which cells each variant names,
and that a group string never spans two physical clusters.  Run with
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q cells/verify/test_rloc_stamp.py"""
import copy
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "hw"))
import rloc_stamp  # noqa: E402


def lut(inputs, outputs, kind="LUT6_2"):
    conns = {f"I{i}": [b] for i, b in enumerate(inputs)}
    dirs = {f"I{i}": "input" for i in range(len(inputs))}
    for i, b in enumerate(outputs):
        port = "O" if len(outputs) == 1 else f"O{5 + i}"
        conns[port], dirs[port] = [b], "output"
    return {"type": kind, "port_directions": dirs, "connections": conns}


def chain(prefix, first, n):
    """`<prefix>.chain.g[i].u`, LUT1s strung bit first -> first+n."""
    return {f"{prefix}.chain.g[{i}].u": lut([first + i], [first + i + 1], "LUT1")
            for i in range(n)}


def netlist():
    top = {
        "ulink_y.ctl.u.u": lut([1, 2, 3], [10], "LUT6"),
        # W=5 bank: two LUT6_2 pairs and an odd bit, enable on I1
        "ulink_y.lat.pair[0].u": lut([20, 10, 30, 21, 31], [30, 31]),
        "ulink_y.lat.pair[1].u": lut([22, 10, 32, 23, 33], [32, 33]),
        "ulink_y.lat.odd.u": lut([24, 10, 34], [34], "LUT6"),
        # a bd_mux whose select (I2) is bit 32, the second pair's O5
        "umux.uj0": lut([40, 41, 32], [42], "LUT6"),
        "umux.uj1": lut([43, 44, 32], [45], "LUT6"),
        "umux.uor.u": lut([42, 45], [46], "LUT2"),
        **chain("ulink_y.udly", 100, 3),
        **chain("uspin", 200, 1),
        "ufused": {"type": "bdc_fused_a", "port_directions": {},
                   "connections": {}},
        "ushared0": {"type": "shared", "port_directions": {},
                     "connections": {}},
        "ushared1": {"type": "shared", "port_directions": {},
                     "connections": {}},
    }
    return {
        "top": {"attributes": {"top": 1}, "cells": top},
        "bdc_fused_a": {"attributes": {}, "cells": chain("udly", 300, 2)},
        "shared": {"attributes": {}, "cells": chain("udly", 400, 2)},
    }


def groups(mods):
    out = {}
    for mname, m in mods.items():
        for cname, c in m["cells"].items():
            g = c.get("attributes", {}).get(rloc_stamp.ATTR)
            if g is not None:
                out.setdefault(g, set()).add(f"{mname}/{cname}")
    return out


def run(variant):
    mods = copy.deepcopy(netlist())
    n_groups, n_cands = rloc_stamp.stamp(mods, variant, report=False)
    return n_groups, n_cands, groups(mods)


def test_v2_names_controller_select_bit_and_consumer_only():
    n_groups, n_cands, g = run("v2")
    assert (n_groups, n_cands) == (1, 1)
    assert g == {"bdlink_ulink_y_ctl_u_u": {
        "top/ulink_y.ctl.u.u", "top/ulink_y.lat.pair[1].u",
        "top/umux.uj0", "top/umux.uj1"}}


def test_v1_drops_the_consumer_but_keeps_the_select_bit():
    _, _, g = run("v1")
    assert g == {"bdlink_ulink_y_ctl_u_u": {
        "top/ulink_y.ctl.u.u", "top/ulink_y.lat.pair[1].u"}}


def test_v3_names_the_whole_bank_and_no_chain():
    _, _, g = run("v3")
    assert g == {"bdlink_ulink_y_ctl_u_u": {
        "top/ulink_y.ctl.u.u", "top/ulink_y.lat.pair[0].u",
        "top/ulink_y.lat.pair[1].u", "top/ulink_y.lat.odd.u",
        "top/umux.uj0", "top/umux.uj1"}}


def test_v4_adds_chains_scoped_by_module():
    _, _, g = run("v4")
    bank = g.pop("bdlink_ulink_y_ctl_u_u")
    assert len(bank) == 6
    assert g == {
        "bddly_ulink_y_udly_chain": {
            f"top/ulink_y.udly.chain.g[{i}].u" for i in range(3)},
        "bddly_bdc_fused_a__udly_chain": {
            f"bdc_fused_a/udly.chain.g[{i}].u" for i in range(2)},
    }


def test_v4_leaves_one_link_chains_and_shared_modules_alone():
    _, _, g = run("v4")
    named = set().union(*g.values())
    assert "top/uspin.chain.g[0].u" not in named
    assert not any(n.startswith("shared/") for n in named)


def test_group_strings_are_unique_per_cluster():
    mods = copy.deepcopy(netlist())
    top = mods["top"]["cells"]
    # a second link with the same local hierarchy inside a second fused cell
    mods["bdc_fused_b"] = {"attributes": {}, "cells": chain("udly", 500, 2)}
    top["ufusedb"] = {"type": "bdc_fused_b", "port_directions": {},
                      "connections": {}}
    rloc_stamp.stamp(mods, "v4", report=False)
    g = groups(mods)
    assert "bddly_bdc_fused_b__udly_chain" in g
    for members in g.values():
        assert len({m.split("/")[0] for m in members}) == 1
