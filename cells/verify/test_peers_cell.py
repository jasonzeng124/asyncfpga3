#!/usr/bin/env python3
"""test_peers_cell.py -- tighten.downstream_of() / site_peers() (BD_PEERS_CELL) on a synthetic routed graph shaped like
test_divui's divider: the request line's tail leaves the cell to a consumer that acknowledges combinationally (the
bench: o_ack = flop & o_req) and the acknowledge comes back in at an OR that opens the datapath (the divider's
hold = join | z_ack).  The old test called that datapath "downstream of the request" and dropped it from rule A's peers;
the cell's acknowledge C-element (bd_mux's uxa = C(j0, z_ack)) is downstream under both tests, and so is anything the
tail reaches inside the cell (a second line hanging off this one)."""
import importlib, os, pathlib, sys
from collections import defaultdict

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.argv = [sys.argv[0], "/nonexistent.sdf"]
import tighten as T                                                     # noqa: E402

P = "top.udut.udiv0"


def graph():
    e = defaultdict(list)

    def arc(a, b, w=100):
        e[a].append((b, w))
    j = P + ".ujoin.u/O6"
    arc(j, P + ".ujoin.u/A3")                      # the join's own loop: storage
    arc(P + ".ujoin.u/A3", j)
    arc(j, P + ".uor/A1"); arc(P + ".uor/A1", P + ".uor/O6")
    arc(P + ".uor/O6", P + ".udly.chain.g[0].u/A1"); arc(P + ".udly.chain.g[0].u/A1", P + ".udly.chain.g[0].u/O6")
    arc(P + ".udly.chain.g[0].u/O6", P + ".udly.chain.g[1].u/A1"); arc(P + ".udly.chain.g[1].u/A1", P + ".udly.chain.g[1].u/O6")
    tail = P + ".udly.chain.g[1].u/O6"
    # the consumer's combinational acknowledge, outside the cell, back in at the hold OR and at an ack C-element
    arc(tail, "top.bench.oack/A1"); arc("top.bench.oack/A1", "top.bench.oack/O6")
    arc("top.bench.oack/O6", P + ".uhold/A2")
    arc(j, P + ".uhold/A1")
    arc(P + ".uhold/A1", P + ".uhold/O6"); arc(P + ".uhold/A2", P + ".uhold/O6")
    arc(P + ".uhold/O6", P + ".dtap[1].u/A1"); arc(P + ".dtap[1].u/A1", P + ".dtap[1].u/O6", 5000)
    arc(P + ".dtap[1].u/O6", P + ".rm0[0].u/A5"); arc(P + ".rm0[0].u/A5", P + ".rm0[0].u/O6", 5000)
    arc(P + ".rm0[0].u/O6", "top.bench.cap/D")                                       # z_data, to the consumer
    arc("top.bench.oack/O6", P + ".ua.u/A1"); arc(P + ".ua.u/A1", P + ".ua.u/O6")
    arc(P + ".ua.u/O6", P + ".ua.u/A2"); arc(P + ".ua.u/A2", P + ".ua.u/O6")          # a C-element: storage
    arc(tail, P + ".after/A1"); arc(P + ".after/A1", P + ".after/O6")                 # inside, off the tail
    arc(P + ".after/O6", "top.bench.x/A1")
    return e, P + ".udly.chain.g[0].u/A1", tail, [P + ".udly.chain.g[0].u", P + ".udly.chain.g[1].u"]


def peers():
    e, head, tail, links = graph()
    stops = T.storage_nodes(e)
    assert stops == {P + ".ujoin.u/O6", P + ".ua.u/O6"}, stops
    return set(T.site_peers(e, stops, P, head, tail, links)), T.downstream_of(e, stops, P, tail)


def test_datapath_behind_the_acknowledge_is_a_peer():
    assert T.PEERS_CELL
    got, down = peers()
    assert P + ".rm0[0].u/O6" in got and P + ".dtap[1].u/O6" in got and P + ".uhold/O6" in got, got
    assert P + ".ua.u/O6" in down and P + ".ua.u/O6" not in got           # the ack C-element: still downstream
    assert P + ".after/O6" in down and P + ".after/O6" not in got         # inside, off the tail: still downstream


def test_old_test_drops_it():                                             # BD_PEERS_CELL=0: the test as it was
    os.environ["BD_PEERS_CELL"] = "0"
    try:
        importlib.reload(T)
        assert not T.PEERS_CELL
        got, _ = peers()
        assert P + ".rm0[0].u/O6" not in got and P + ".dtap[1].u/O6" not in got and P + ".uhold/O6" not in got, got
    finally:
        del os.environ["BD_PEERS_CELL"]
        importlib.reload(T)


def test_rule_a_measures_it():
    """check() from the join (the common source): the data peak runs through the hold OR, the enable and the stage
    (100 + 100 + 100 + 5000 + 100 + 5000 = 10400 ps after the join) against the request at the tail (six 100 ps arcs:
    600 ps)."""
    e, head, tail, links = graph()
    stops = T.storage_nodes(e)
    tm = T.Timing(e, stops)
    pe = T.site_peers(e, stops, P, head, tail, links)
    srcs = T.cell_boundary(e, defaultdict(set, {d: {s} for s, l in e.items() for d, _ in l}), stops, P)
    r = T.check(tm, srcs, pe, tail, lambda p, t: 0, confine=P)
    assert r is not None and r[3] == 10400 and r[2] == 600 and r[0] == 600 - 10400, r


if __name__ == "__main__":
    for f in (test_datapath_behind_the_acknowledge_is_a_peer, test_old_test_drops_it, test_rule_a_measures_it):
        f()
        print("ok", f.__name__)
