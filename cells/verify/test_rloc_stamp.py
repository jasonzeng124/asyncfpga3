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


def ring_netlist():
    """Two links whose handshake ring crosses into a fused compute module:
    C_a -> (req port) uor -> udly chain -> (out port) -> C_b -> ack -> C_a,
    C_a also owning a one-link ack delay, and a LUT that drives reset."""
    top = {
        "ulink_a.ctl.u.u": lut([1, 60], [10], "LUT6"),
        "ulink_a.lat.pair[0].u": lut([20, 10, 30, 21, 31], [30, 31]),
        "ulink_a.lat.pair[1].u": lut([22, 10, 32, 23, 33], [32, 33]),
        **chain("ulink_a.uack", 10, 1),
        "ufused": {"type": "bdc_fused_a", "port_directions": {
            "req": "input", "out": "output"},
            "connections": {"req": [10], "out": [50]}},
        "ulink_b.ctl.u.u": lut([50, 7], [60], "LUT6"),
        "ulink_b.lat.pair[0].u": lut([30, 60, 70, 31, 71], [70, 71]),
        "ulink_b.lat.pair[1].u": lut([32, 60, 72, 33, 73], [72, 73]),
        "urst.u": lut([8], [7], "LUT1"),
    }
    fused = {"uor": lut([1, 5], [2], "LUT2"), **chain("udly", 2, 3)}
    return {
        "top": {"attributes": {"top": 1}, "cells": top,
                "netnames": {"rst": {"bits": [7]}}},
        "bdc_fused_a": {"attributes": {"keep_hierarchy": 1}, "cells": fused,
                        "ports": {"req": {"bits": [1]}, "out": {"bits": [5]}}},
    }


def test_v5_banks_without_controller_and_one_slot_ordered_spine():
    mods = ring_netlist()
    n_groups, n_cands = rloc_stamp.stamp(mods, "v5", report=False)
    assert (n_groups, n_cands) == (3, 2)
    g = groups(mods)
    assert g["bdlink_ulink_a_ctl_u_u"] == {
        "top/ulink_a.lat.pair[0].u", "top/ulink_a.lat.pair[1].u"}
    assert g["bdlink_ulink_b_ctl_u_u"] == {
        "top/ulink_b.lat.pair[0].u", "top/ulink_b.lat.pair[1].u"}
    spine = {k: v for k, v in g.items() if k.startswith("bdspine_")}
    assert len(spine) == 1
    (members,) = spine.values()
    slot = {}
    for mname, m in mods.items():
        for cname, c in m["cells"].items():
            a = c.get("attributes", {})
            if a.get(rloc_stamp.ATTR) in spine:
                slot[a[rloc_stamp.SLOT_ATTR]] = f"{mname}/{cname}"
    # in the order a transition travels: the ack link hangs off C_a, then
    # request out through the fused cone's OR and chain to C_b
    assert [slot[i] for i in range(len(slot))] == [
        "top/ulink_a.uack.chain.g[0].u", "top/ulink_a.ctl.u.u",
        "bdc_fused_a/uor", "bdc_fused_a/udly.chain.g[0].u",
        "bdc_fused_a/udly.chain.g[1].u", "bdc_fused_a/udly.chain.g[2].u",
        "top/ulink_b.ctl.u.u"]
    assert members == set(slot.values())
    # reset is not a handshake net: its driver joins no spine
    assert rloc_stamp.ATTR not in mods["top"]["cells"]["urst.u"].get("attributes", {})


def test_v5_splits_a_long_spine_into_segments_in_order():
    mods = ring_netlist()
    # a 40-link request chain: with C_a, the OR and C_b that is more than one
    # 32-slot segment
    mods["bdc_fused_a"]["cells"] = {"uor": lut([1, 42], [2], "LUT2"),
                                    **chain("udly", 2, 40)}
    mods["bdc_fused_a"]["ports"]["out"]["bits"] = [42]
    rloc_stamp.stamp(mods, "v5", report=False)
    spine = {k: v for k, v in groups(mods).items() if k.startswith("bdspine_")}
    assert sorted(len(v) for v in spine.values()) == [12, 32]
    for members in spine.values():
        slots = sorted(
            mods[m.split("/")[0]]["cells"][m.split("/", 1)[1]]["attributes"][rloc_stamp.SLOT_ATTR]
            for m in members)
        assert slots == list(range(len(members)))


def slot_order(mods, group):
    slot = {}
    for mname, m in mods.items():
        for cname, c in m["cells"].items():
            a = c.get("attributes", {})
            if a.get(rloc_stamp.ATTR) == group:
                slot[a[rloc_stamp.SLOT_ATTR]] = f"{mname}/{cname}"
    assert sorted(slot) == list(range(len(slot)))
    return [slot[i] for i in range(len(slot))]


def test_v6_threads_the_spine_through_each_bank():
    mods = ring_netlist()
    n_groups, n_cands = rloc_stamp.stamp(mods, "v6", report=False)
    assert (n_groups, n_cands) == (1, 2)
    g = groups(mods)
    assert not any(k.startswith("bdlink_") for k in g)
    (name,) = g
    # v5's order with each bank split around its own C node
    assert slot_order(mods, name) == [
        "top/ulink_a.uack.chain.g[0].u",
        "top/ulink_a.lat.pair[0].u", "top/ulink_a.ctl.u.u", "top/ulink_a.lat.pair[1].u",
        "bdc_fused_a/uor", "bdc_fused_a/udly.chain.g[0].u",
        "bdc_fused_a/udly.chain.g[1].u", "bdc_fused_a/udly.chain.g[2].u",
        "top/ulink_b.lat.pair[0].u", "top/ulink_b.ctl.u.u", "top/ulink_b.lat.pair[1].u"]


def test_v6_never_splits_a_bank_from_its_controller():
    mods = ring_netlist()
    mods["bdc_fused_a"]["cells"] = {"uor": lut([1, 42], [2], "LUT2"),
                                    **chain("udly", 2, 70)}
    mods["bdc_fused_a"]["ports"]["out"]["bits"] = [42]
    rloc_stamp.stamp(mods, "v6", report=False)
    g = groups(mods)
    # 1 + 3 + 1 + 70 + 3 = 78 slots: the 64-slot boundary falls inside the
    # chain, and C_b's three-cell atom stays whole in the second segment
    assert sorted(len(v) for v in g.values()) == [14, 64]
    for name, members in g.items():
        order = slot_order(mods, name)
        assert set(order) == members
        for i, c in enumerate(order):
            if c.endswith(".ctl.u.u"):
                assert order[i - 1].endswith(".lat.pair[0].u")
                assert order[i + 1].endswith(".lat.pair[1].u")


def placement(mods, name):
    c = mods["top"]["cells"][name].get("attributes", {})
    return (c.get(rloc_stamp.ATTR), c.get(rloc_stamp.COL_ATTR), c.get(rloc_stamp.SLOT_ATTR))


def test_v7_puts_the_data_path_beside_the_spine_at_the_row_of_its_latches():
    mods = ring_netlist()
    top = mods["top"]["cells"]
    # a's bank feeds two abc LUTs, one through the other, into b's bank
    top["$abc$1$x0"] = lut([30, 31], [80], "LUT2")
    top["$abc$1$x1"] = lut([80, 32], [81], "LUT2")
    top["ulink_b.lat.pair[0].u"] = lut([81, 60, 70, 31, 71], [70, 71])
    # a LUT on nets that reach no spine at all stays with the placer
    top["$abc$1$island"] = lut([90, 91], [92], "LUT2")
    n_groups, n_cands = rloc_stamp.stamp(mods, "v7", report=False)
    assert (n_groups, n_cands) == (1, 2)
    (spine,) = groups(mods)
    # the spine itself is v6's, in column 0
    col0 = {}
    for cname, c in top.items():
        a = c.get("attributes", {})
        if a.get(rloc_stamp.ATTR) == spine and not a.get(rloc_stamp.COL_ATTR):
            col0[a[rloc_stamp.SLOT_ATTR]] = cname
    assert col0[2] == "ulink_a.ctl.u.u" and col0[9] == "ulink_b.ctl.u.u"
    assert "$abc$1$x0" not in col0.values()
    # x0 is pulled toward a's bank (slot 1) and x1, x1 toward x0 and b's
    # bank (slot 8): both land between the banks, in a side column of the
    # same group, x1 the further along
    g0, c0, s0 = placement(mods, "$abc$1$x0")
    g1, c1, s1 = placement(mods, "$abc$1$x1")
    assert g0 == g1 == spine
    assert {c0, c1} <= {-1, 1}
    assert 1 <= s0 <= s1 <= 8
    assert placement(mods, "$abc$1$island") == (None, None, None)


def test_v7_side_slots_are_unique_and_within_the_column():
    mods = ring_netlist()
    top = mods["top"]["cells"]
    # 40 LUTs all wanting slot 1: each side column has slots 0..17 within
    # reach of it, the rest are left to the placer
    for i in range(40):
        top[f"$abc$2$y{i}"] = lut([30, 31], [100 + i], "LUT2")
    rloc_stamp.stamp(mods, "v7", report=False)
    taken, loose = set(), 0
    for cname, c in top.items():
        a = c.get("attributes", {})
        if not cname.startswith("$abc$"):
            continue
        if rloc_stamp.ATTR not in a:
            loose += 1
            continue
        key = (a[rloc_stamp.COL_ATTR], a[rloc_stamp.SLOT_ATTR])
        assert key not in taken
        assert 0 <= key[1] <= 1 + rloc_stamp.SIDE_REACH
        taken.add(key)
    assert len(taken) == 2 * (rloc_stamp.SIDE_REACH + 2) and loose == 4


def rows(mods, group):
    """{cell: (col, row, slot in row)} of a group's members."""
    out = {}
    for mname, m in mods.items():
        for cname, c in m["cells"].items():
            a = c.get("attributes", {})
            if a.get(rloc_stamp.ATTR) == group:
                s = a[rloc_stamp.SLOT_ATTR]
                out[f"{mname}/{cname}"] = (a.get(rloc_stamp.COL_ATTR, 0),
                                           s // rloc_stamp.ROW_SLOTS, s % rloc_stamp.ROW_SLOTS)
    return out


def test_v8_gives_each_controller_a_row_with_the_ends_of_its_chains():
    mods = ring_netlist()
    mods["bdc_fused_a"]["cells"] = {"uor": lut([1, 12], [2], "LUT2"),
                                    **chain("udly", 2, 10)}
    mods["bdc_fused_a"]["ports"]["out"]["bits"] = [12]
    n_groups, n_cands = rloc_stamp.stamp(mods, "v8", report=False)
    assert (n_groups, n_cands) == (1, 2)
    (name,) = groups(mods)
    at = rows(mods, name)
    assert len({v for v in at.values()}) == len(at)
    # C_a's row: its ack link before it, the OR and the first three links
    # after it; a's bank halves are the rows either side
    assert at["top/ulink_a.ctl.u.u"] == (0, 1, 1)
    assert at["top/ulink_a.uack.chain.g[0].u"] == (0, 1, 0)
    assert [at[f"bdc_fused_a/udly.chain.g[{i}].u"] for i in range(3)] == [
        (0, 1, 3), (0, 1, 4), (0, 1, 5)]
    assert at["bdc_fused_a/uor"] == (0, 1, 2)
    assert at["top/ulink_a.lat.pair[0].u"][1] == 0
    assert at["top/ulink_a.lat.pair[1].u"][1] == 2
    # the chain's middle fills the rows before b's bank; its last three
    # links open C_b's row
    assert [at[f"bdc_fused_a/udly.chain.g[{i}].u"][1] for i in range(3, 7)] == [2] * 4
    assert [at[f"bdc_fused_a/udly.chain.g[{i}].u"] for i in range(7, 10)] == [
        (0, 4, 0), (0, 4, 1), (0, 4, 2)]
    assert at["top/ulink_b.ctl.u.u"] == (0, 4, 3)
    assert at["top/ulink_b.lat.pair[0].u"][1] == 3
    assert at["top/ulink_b.lat.pair[1].u"][1] == 5


def test_v8_fills_the_gaps_of_a_row_with_the_data_path_first():
    mods = ring_netlist()
    top = mods["top"]["cells"]
    top["$abc$1$x0"] = lut([30, 31], [80], "LUT2")
    top["$abc$1$x1"] = lut([80, 32], [81], "LUT2")
    top["ulink_b.lat.pair[0].u"] = lut([81, 60, 70, 31, 71], [70, 71])
    rloc_stamp.stamp(mods, "v8", report=False)
    (name,) = groups(mods)
    at = rows(mods, name)
    assert len({v for v in at.values()}) == len(at)
    # x0 sits between a's bank halves, so C_a's row: it has two slots free
    # past the chain, and one of them wins over the side columns.  x1 is
    # pulled a row further, where the bank fills the spine, so it goes beside.
    assert at["top/$abc$1$x0"] == (0, 1, 6)
    assert at["top/$abc$1$x1"][:2] in {(-1, 2), (1, 2)}


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
