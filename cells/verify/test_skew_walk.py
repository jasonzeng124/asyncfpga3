"""Rule E's walk: every replayed chain must be the one that set the arrival.

skew.walk() keeps one arrival table and one predecessor table per storage
crossing level, and skew.path_to() replays a pin's predecessors back to the
launch.  divergence() (t_c) and req_knob() (which link to pad) read that
replay, so a chain that did not produce the arrival it ends in silently
corrupts both.  These are the two minimal shapes in which the walk used to
overwrite a node SEEDED at a level -- a storage output entered by its one
deliberate crossing, or the launch itself -- with a later arrival from inside
the same level, after the seed had already been expanded.
"""
from collections import defaultdict
import sys

sys.path.insert(0, str(__file__).rsplit("/", 2)[0])
import tighten as T

_argv = sys.argv[:]
sys.argv = _argv[:1]            # skew.py reads its own argv at import time
try:
    import skew
finally:
    sys.argv = _argv


def storage(edges, inst, inputs, arc=10):
    """A LUT that holds: its output feeds its own A6, and every input
    (including A6) has a cell arc to the output."""
    out = f"{inst}/O6"
    edges[out].append((f"{inst}/A6", 1))
    for pin in inputs + ["A6"]:
        edges[f"{inst}/{pin}"].append((out, arc))
    return out


def graph(edges):
    stops = T.storage_nodes(edges)
    binc, srcs_of = defaultdict(list), defaultdict(set)
    for s, lst in edges.items():
        for d, w in lst:
            binc[d].append((s, w))
            srcs_of[d].add(s)
    feed = {(o, ip) for o in stops
            for ip, _ in binc.get(o, ()) if o in srcs_of[ip]}
    return stops, binc, feed


def assert_consistent(edges, out, chain):
    """Each step of a replayed chain adds exactly its own arc's delay."""
    w = {(s, d): x for s, lst in edges.items() for d, x in lst}
    for (la, a), (lb, b) in zip(chain, chain[1:]):
        assert out[lb][b] == out[la][a] + w[(a, b)], (a, b)


def test_seeded_stop_is_not_overwritten_inside_its_level():
    # L launches.  S is reached at level 1 through its own crossing from
    # S/A1 (100 + 10), and expanded from there to the request pin G/A1.
    # T is reached cheaply (5 + 10) and, INSIDE level 1, offers S a far
    # earlier arrival through S/A2 -- which is itself a crossing of S.
    edges = defaultdict(list)
    launch = storage(edges, "L", ["A1"])
    s_out = storage(edges, "S", ["A1", "A2"])
    t_out = storage(edges, "T", ["A1"])
    edges[launch] += [("S/A1", 100), ("T/A1", 5)]
    edges[t_out].append(("S/A2", 5))
    edges[s_out].append(("G/A1", 50))
    stops, binc, feed = graph(edges)
    assert {launch, s_out, t_out} <= stops

    out, pred = skew.walk(edges, stops, binc, feed, launch, longest=False)
    # The arrival is the one the seed was expanded with, and the fix must not
    # move it: 100 + 10 (S's crossing) + 50.
    assert out[1]["G/A1"] == 160
    chain = skew.path_to(pred, 1, "G/A1")
    assert chain == [(0, launch), (0, "S/A1"), (1, s_out), (1, "G/A1")]
    assert out[1][s_out] == 110
    assert_consistent(edges, out, chain)


def test_launch_is_not_overwritten_by_its_own_loop_at_level_0():
    # A storage-free path from the launch back into its own A1.  A LONGEST
    # walk used to record that lap AT the launch, giving the launch a
    # predecessor, so every replay from it closed on itself and returned
    # None (divergence() then fell back to t_c = 0).
    edges = defaultdict(list)
    launch = storage(edges, "L", ["A1"])
    edges[launch] += [("C/A1", 7), ("G/A1", 40)]
    edges["C/A1"].append(("C/O6", 10))
    edges["C/O6"].append(("L/A1", 3))
    stops, binc, feed = graph(edges)
    assert "C/O6" not in stops

    out, pred = skew.walk(edges, stops, binc, feed, launch, longest=True)
    assert out[0][launch] == 0
    chain = skew.path_to(pred, 0, "G/A1")
    assert chain == [(0, launch), (0, "G/A1")]
    assert_consistent(edges, out, chain)
