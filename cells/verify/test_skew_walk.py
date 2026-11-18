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


def test_and_join_waits_for_its_last_reached_input():
    # L launches two requests into a 2-input join J (a bd_ctree C-element):
    # one short (5) and one long (300).  OR seeding (default) fires J on the
    # short one; with J in AND_NODES the request walk waits for the long one.
    edges = defaultdict(list)
    launch = storage(edges, "L", ["A1"])
    j = "X.j.u.g2.u.u"
    j_out = storage(edges, j, ["A1", "A2"])
    edges[launch] += [(f"{j}/A1", 5), (f"{j}/A2", 300)]
    edges[j_out].append(("G/A1", 20))
    stops, binc, feed = graph(edges)
    assert skew.RE_CTREE_C.search(j_out)
    skew.AND_NODES.clear()
    out, _ = skew.walk(edges, stops, binc, feed, launch, longest=False)
    assert out[1]["G/A1"] == 5 + 10 + 20
    skew.AND_NODES.add(j_out)
    try:
        out, pred = skew.walk(edges, stops, binc, feed, launch, longest=False)
        assert out[1]["G/A1"] == 300 + 10 + 20
        assert skew.path_to(pred, 1, "G/A1")[1] == (0, f"{j}/A2")
        # the LONGEST (select) walk is never changed by it
        lo, _ = skew.walk(edges, stops, binc, feed, launch, longest=True)
        assert lo[1]["G/A1"] == 330
    finally:
        skew.AND_NODES.clear()



def test_steer_self_floor_counts_the_channel_request_not_a_lap():
    # (5) --steer-self.  Link A (C node C, latch X) feeds a compare P: X ->
    # P's data -> the steer's select pin; C -> P's operand join -> P.uor ->
    # P's delay -> one input (A2) of the steer's request join J.  J's other
    # input (A1) is a sibling link's request, which C's walk reaches only by a
    # lap: through X, the steer's own LUT and acknowledge, and the sibling's
    # controller.  The bound must come from A2 only.
    edges = defaultdict(list)
    c_out = storage(edges, "K.ulink_a.ctl.u.u", ["A1", "A2"])
    x_out = storage(edges, "K.ulink_a.lat.pair[0].u$LUT5", ["A1", "A2"])
    jn = storage(edges, "K.ucmp.ujoin.u.g2.u.u", ["A1", "A2"])
    sib = storage(edges, "K.usib.ctl.u.u", ["A1", "A2"])
    j_out = storage(edges, "K.ust_j.u.g2.u.u", ["A1", "A2"])
    edges[c_out] += [("K.ulink_a.lat.pair[0].u$LUT5/A1", 100), ("K.ucmp.ujoin.u.g2.u.u/A1", 50)]
    edges[jn].append(("K.ucmp.uor/A1", 20))
    edges["K.ucmp.uor/A1"].append(("K.ucmp.uor/O6", 10))
    edges["K.ucmp.uor/O6"].append(("K.ucmp.udly.chain.g[0].u/A1", 30))
    edges["K.ucmp.udly.chain.g[0].u/A1"].append(("K.ucmp.udly.chain.g[0].u/O6", 100))
    tail = "K.ucmp.udly.chain.g[0].u/O6"
    edges[tail].append(("K.ust_j.u.g2.u.u/A2", 40))
    edges[x_out].append(("K.ucmp.uz/A1", 15))
    edges["K.ucmp.uz/A1"].append(("K.ucmp.uz/O6", 10))
    edges["K.ucmp.uz/O6"].append(("K.ust.u$LUT5/A4", 25))           # the select pin
    edges["K.ust.u$LUT5/A4"].append(("K.ust.u$LUT5/O5", 10))         # through the gate itself
    edges["K.ust.u$LUT5/O5"].append(("K.ust.uack/A1", 5))
    edges["K.ust.uack/A1"].append(("K.ust.uack/O6", 10))
    edges["K.ust.uack/O6"].append(("K.usib.ctl.u.u/A2", 5))          # the sibling's acknowledge
    edges[sib].append(("K.ust_j.u.g2.u.u/A1", 5))
    edges[j_out].append(("K.ust.u$LUT5/A1", 20))                      # the request pin
    stops, binc, feed = graph(edges)
    skew.AND_NODES.clear()
    skew.AND_NODES.update({jn, j_out})
    try:
        ce = skew.walk(edges, stops, binc, feed, c_out, longest=False)
        cl = skew.walk(edges, stops, binc, feed, c_out, longest=True)
        inside = ("K.ulink_a.", "K.ucmp.")
        fl = skew.self_request_floor(ce[0], ce[1], cl[0], j_out, x_out, binc, feed, stops,
                                     inside, {jn}, tail)
        # s(C -> J/A2) = 50 + 10 (join) + 20 + 10 + 30 + 100 + 40 = 260, + J's arc 10;
        # l(C -> X) = 100 + 10.  Bound relative to X: 270 - 110.
        assert fl is not None
        floor, l_cx, ip, lvl, chain = fl
        assert (floor, l_cx, ip, lvl) == (160, 110, "K.ust_j.u.g2.u.u/A2", 1)
        assert chain[0] == (0, c_out) and chain[-1] == (1, "K.ust_j.u.g2.u.u/A2")
        # X's own request walk reaches J only through the lap, earlier than the bound:
        xe, _ = skew.walk(edges, stops, binc, feed, x_out, longest=False)
        assert xe[2]["K.ust.u$LUT5/A1"] == 15 + 10 + 25 + 10 + 5 + 10 + 5 + 10 + 5 + 10 + 20
        assert xe[2]["K.ust.u$LUT5/A1"] < floor + 20
        # The same request leaving the producer through anything outside it (a
        # merge's OR, here an instance not in `inside`) gives no bound.
        assert skew.self_request_floor(ce[0], ce[1], cl[0], j_out, x_out, binc, feed, stops,
                                       ("K.ulink_a.",), {jn}, tail) is None
        # ... nor does a chain that misses the producer's request output.
        assert skew.self_request_floor(ce[0], ce[1], cl[0], j_out, x_out, binc, feed, stops,
                                       inside, {jn}, "K.ucmp.uz/O6") is None
        # ... nor one whose join is not the producer's own.
        assert skew.self_request_floor(ce[0], ce[1], cl[0], j_out, x_out, binc, feed, stops,
                                       inside, set(), tail) is None
        # A launch C does not open (not reached at level 0 of C's latest walk): no bound.
        assert skew.self_request_floor(ce[0], ce[1], cl[0], j_out, sib, binc, feed, stops,
                                       inside, {jn}, tail) is None
    finally:
        skew.AND_NODES.clear()

if __name__ == "__main__":
    for n, f in list(globals().items()):
        if n.startswith("test_") and callable(f):
            f(); print("ok", n)
