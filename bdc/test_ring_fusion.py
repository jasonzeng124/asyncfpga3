"""BDC_RING_FUSE: a region merges with the fusable reader of the fork that splits its result, and the merged region
has one result per value that leaves it.  The loop's update and test (`x' = x + y; c = x' < n; steer(c, x')`) are the
shape it exists for; the refusals below are the ones that keep it from deadlocking.

The deadlock refusal has a negative control on a real kernel as well (research/data/ringfuse/README.md): with the
check removed, memsum's merge {addi2, cmpi1, cmpi2, andi0} hangs memtb at its first call; with it, memtb passes.
"""
import pytest

from test_fusion_sharing import F, N
import emit


def B(op, operands=(), results=(), bb=1, **attrs):
    attrs["handshake.bb"] = bb
    return N(op, operands, results, attrs=attrs)


def ring(bb_of_test=1):
    """merge -> addi -> fork -> {cmpi, cond_br data}; cmpi -> cond_br condition; cond_br true -> merge."""
    return F([
        B("merge", ["x0", "t"], ["x"]),
        B("addi", ["x", "y"], ["x1"]),
        B("fork", ["x1"], ["x1a", "x1b"]),
        B("cmpi", ["x1a", "n"], ["c"], bb=bb_of_test),
        B("cond_br", ["c", "x1b"], ["t", "f"]),
        N("sink", ["f"]),
    ])


@pytest.fixture
def ring_fuse(monkeypatch):
    monkeypatch.setattr(emit, "RING_FUSE", True)
    monkeypatch.setattr(emit, "RING_FUSE_MAX", 8)


def test_off_keeps_two_regions(monkeypatch):
    monkeypatch.setattr(emit, "RING_FUSE", False)
    plan = emit.compute_fusion(ring(), forks=True)
    assert sorted(plan.anchor_region) == [1, 3]
    assert 2 not in plan.skip
    assert all(r.outputs is None for r in plan.anchor_region.values())


def test_update_and_test_merge(ring_fuse):
    plan = emit.compute_fusion(ring(), forks=True)
    assert list(plan.anchor_region) == [3]
    region = plan.anchor_region[3]
    assert region.node_ids == [1, 3]
    assert region.ext_inputs == ["x", "y", "n"]
    assert region.outputs == [("c", 3), ("x1b", 1)]          # the test's result, then the fork output that leaves
    assert region.ref[(3, "a")] == ("wire", 1)                 # the compare reads the adder inside the cell
    assert {1, 2} <= plan.skip and 3 not in plan.skip
    assert {"x1", "x1a"} <= plan.dead_values
    assert "x1b" not in plan.dead_values and "c" not in plan.dead_values


def test_other_block_refused(ring_fuse):
    plan = emit.compute_fusion(ring(bb_of_test=2), forks=True)
    assert sorted(plan.anchor_region) == [1, 3]


def test_cap_refused(monkeypatch):
    monkeypatch.setattr(emit, "RING_FUSE", True)
    monkeypatch.setattr(emit, "RING_FUSE_MAX", 1)
    plan = emit.compute_fusion(ring(), forks=True)
    assert sorted(plan.anchor_region) == [1, 3]


def test_same_firing_cycle_refused(ring_fuse):
    """memsum's shape: the fork's third output reaches the merged region again through a node that is not fused
    (extui), so the merged cell would wait for its own result.  The merge must be refused."""
    graph = F([
        B("merge", ["x0", "t"], ["x"]),
        B("addi", ["x", "y"], ["x1"]),
        B("fork", ["x1"], ["x1a", "x1b", "x1c"]),
        B("extui", ["x1c"], ["w"]),
        B("cmpi", ["w", "n"], ["c1"]),
        B("cmpi", ["x1a", "m"], ["c2"]),
        B("andi", ["c1", "c2"], ["c"]),
        B("cond_br", ["c", "x1b"], ["t", "f"]),
        N("sink", ["f"]),
    ])
    plan = emit.compute_fusion(graph, forks=True)
    assert 2 not in plan.skip
    assert all(r.outputs is None for r in plan.anchor_region.values())
    assert sorted(plan.anchor_region) == [1, 6]


def test_cycle_through_a_loop_header_is_allowed(ring_fuse):
    """The leaving output goes round the loop (cond_br -> merge -> addi): a later firing, not a deadlock."""
    plan = emit.compute_fusion(ring(), forks=True)
    assert plan.anchor_region[3].outputs is not None
