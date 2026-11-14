"""Graph contraction and streamed RTL checks for reconvergent fork fusion."""

from dataclasses import replace

import pytest

import emit
import fusion_bench as bench
from hs import parse
from test_fusion_sharing import F, N, _graph


def plan_for(name, cap=4, reverse=False):
    func = parse.parse_module(bench.fixture(name)[0])[0]
    if reverse:
        func = replace(func, nodes=list(reversed(func.nodes)))
    return func, emit.compute_fusion(func, forks=True, max_nodes=cap)


@pytest.mark.parametrize("reverse", [False, True])
@pytest.mark.parametrize("cap,regions", [(2, 3), (4, 2), (8, 1)])
def test_xorshift_partition(cap, regions, reverse):
    func, plan = plan_for("xorshift_round", cap, reverse)
    assert len(plan.anchor_region) == regions
    assert sum(func.nodes[i].op == "fork" for i in plan.skip) == 3
    for region in plan.anchor_region.values():
        assert len(region.node_ids) <= cap
        assert len(region.ext_inputs) == 1
        position = {i: k for k, i in enumerate(region.node_ids)}
        for (i, _), (kind, value) in region.ref.items():
            if kind == "wire":
                assert position[value] < position[i]


def test_fork_with_external_consumer_stays():
    graph = F([
        N("fork", ["x"], ["a", "b", "escape"]),
        N("addi", ["a", "b"], ["sum"]),
        N("sink", ["sum"]),
        N("sink", ["escape"]),
    ])
    plan = emit.compute_fusion(graph, forks=True)
    assert 0 not in plan.skip
    assert plan.anchor_region[1].ext_inputs == ["a", "b"]


def test_nested_forks_collapse_to_one_join_input():
    graph = F([
        N("fork", ["x"], ["a", "b"]),
        N("fork", ["a"], ["c", "d"]),
        N("addi", ["c", "d"], ["sum"]),
        N("xori", ["sum", "b"], ["result"]),
        N("sink", ["result"]),
    ])
    plan = emit.compute_fusion(graph, forks=True)
    assert {0, 1, 2} <= plan.skip
    assert plan.anchor_region[3].ext_inputs == ["x"]
    assert {"a", "b", "c", "d", "sum"} <= plan.dead_values


@pytest.mark.parametrize("boundary", ["mux", "cond_br", "load", "lazy_fork"])
def test_control_and_memory_boundaries_stay(boundary):
    graph = F([
        N("fork", ["x"], ["a", "b"]),
        N(boundary, ["a"], ["z"]),
        N("addi", ["b", "z"], ["result"]),
        N("sink", ["result"]),
    ])
    plan = emit.compute_fusion(graph, forks=True)
    assert not {0, 1} & plan.skip
    assert plan.anchor_region[2].ext_inputs == ["b", "z"]


def test_fork_cycle_does_not_become_combinational_feedback():
    graph = F([
        N("fork", ["result"], ["a", "b"]),
        N("addi", ["a", "b"], ["result"]),
    ])
    plan = emit.compute_fusion(graph, forks=True)
    assert 0 not in plan.skip


def test_unmaterialized_fork_output_does_not_disappear():
    graph = F([
        N("fork", ["x"], ["a", "b"]),
        N("addi", ["a", "a"], ["sum"]),
        N("xori", ["sum", "b"], ["result"]),
        N("sink", ["result"]),
    ])
    assert 0 not in emit.compute_fusion(graph, forks=True).skip


def test_shared_constant_source_remains_live():
    plan = emit.compute_fusion(_graph(extra_reader_of="s0"), forks=True)
    assert not {0, 1} & plan.skip


def test_slack_stage_between_logic_off_cycles_only():
    # x -> mux -> add -> fork, one arm back to the mux, the other through a
    # fork to an xori and out.  The ring's channels keep what ring_depths()
    # said; x comes from a port (nothing upstream to overlap) and g#1 goes
    # straight to the output (nothing downstream); g#0 has the add behind it
    # through two forks and the xori ahead of it, and is the one site.
    src = """
handshake.func @ring(%x: !handshake.channel<i32>, %sel: !handshake.channel<i1>, ...) -> !handshake.channel<i32> attributes {argNames = ["x", "sel"], resNames = ["out"]} {
    %m = mux %sel [%x, %fb] : <i1>, [<i32>, <i32>] to <i32>
    %s = addi %m, %m : <i32>
    %f:2 = fork [2] %s : <i32>
    %fb = buffer %f#0 : <i32>
    %g:2 = fork [2] %f#1 : <i32>
    %y = xori %g#0, %g#0 : <i32>
    end %y, %g#1 : <i32>, <i32>
}
"""
    func = parse.parse_module(src)[0]
    linked = {"x", "fb", "m", "g#0", "g#1"}
    assert emit.slack_sites(func, linked) == {"g#0"}
    # a link on f#1 as well: it hides the add from g#0, and sees no logic
    # itself before the next links
    assert emit.slack_sites(func, linked | {"f#1"}) == set()
    assert emit.slack_sites(func, (linked - {"g#0"}) | {"f#1"}) == {"f#1"}
    depth = {"fb": 3}
    assert emit._apply_slack_stages(func, linked, depth) == {"g#0"}
    assert depth == {"fb": 3, "g#0": 2}
    assert emit._apply_slack_stages(func, linked, depth, exclude={"g#0"}) == set()
    func, _ = plan_for("xorshift_round")
    assert emit.slack_sites(func, {"x", "v9"}) == {"v9"}


def test_invalid_cap():
    with pytest.raises(emit.EmitError, match="at least 1"):
        emit.compute_fusion(F([]), max_nodes=0)


@pytest.mark.parametrize("cap", [1, 2, 4, 8])
@pytest.mark.parametrize("name", bench.FIXTURES)
def test_streamed_results_with_skew_and_backpressure(name, cap, tmp_path, monkeypatch):
    monkeypatch.setattr(emit, "BDC_OP_FUSION", True)
    monkeypatch.setattr(emit, "BDC_FORK_FUSION", True)
    monkeypatch.setattr(emit, "MAX_FUSE_NODES", cap)
    bench.measure(name, tmp_path / name, stalls=True)
