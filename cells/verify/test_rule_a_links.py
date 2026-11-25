from collections import defaultdict
import sys

sys.path.insert(0, str(__file__).rsplit("/", 2)[0])
import tighten


def test_upstream_bd_links_recognizes_link_shapes():
    srcs = {
        "u1.lat.odd.u$LUT6/O6",
        "u8.lat.pair[3].u$LUT5/O5",
        "pipe3.many.stage[2].u.ctl.u.u/O6",
        "pipe3.many.stage[2].u.lat.odd.u$LUT6/O6",
        "pipe2.many.stage[1].u.ctl.u.u/O6",
        "pipe2.many.stage[1].u.lat.pair[0].u$LUT5/O5",
        "pipe1.one.u.ctl.u.u/O6",
        "unrelated/O6",
    }
    assert tighten.upstream_bd_links(srcs) == (
        "pipe1.one.u",
        "pipe2.many.stage[1].u",
        "pipe3.many.stage[2].u",
        "u1",
        "u8",
    )


def add_latch(edges, controller, latch, ctl_delay, latch_delay):
    input_pin = f"{latch}/I0"
    output_pin = f"{latch}/O6"
    edges[controller].append((input_pin, ctl_delay))
    edges[input_pin].append((output_pin, latch_delay))
    return controller, output_pin


def test_upstream_data_lag_uses_final_latch_controller_paths():
    edges = defaultdict(list)
    pairs = [
        add_latch(
            edges,
            "pipe3.many.stage[2].u.ctl.u.u/O6",
            "pipe3.many.stage[2].u.lat.odd.u$LUT6",
            7,
            13,
        ),
        add_latch(
            edges,
            "pipe2.many.stage[1].u.ctl.u.u/O6",
            "pipe2.many.stage[1].u.lat.pair[0].u$LUT5",
            11,
            17,
        ),
    ]
    stops = {pin for pair in pairs for pin in pair}
    timing = tighten.Timing(edges, stops)
    back = defaultdict(set)
    for source, links in edges.items():
        for destination, _ in links:
            back[destination].add(source)
    srcs = {pair[1] for pair in pairs}

    assert tighten.upstream_data_lag(
        timing, back, None,
        ("pipe2.many.stage[1].u", "pipe3.many.stage[2].u"), srcs,
    ) == 28


def test_ack_chain_knob():
    knob = lambda b: tighten.RE_ACK_CHAIN.match(b).group(1) + ".uack"
    assert knob("uut.ulink_n_x.uack") == "uut.ulink_n_x.uack"
    assert knob("upipe.one.u.uack") == "upipe.uack"
    assert knob("upipe.many.stage[3].u.uack") == "upipe.uack"


def add_chain(edges, base, luts, hops, feed="drv/O6"):
    """A bd_delay chain as the routed SDF has it: link i is a LUT whose A1->O6
    arc is luts[i], and hops[i] is the routed wire from link i to link i+1."""
    links = [f"{base}.chain.g[{i}].u" for i in range(len(luts))]
    edges[feed].append((f"{links[0]}/A1", 300))
    for i, link in enumerate(links):
        edges[f"{link}/A1"].append((f"{link}/O6", luts[i]))
        if i + 1 < len(links):
            edges[f"{link}/O6"].append((f"{links[i + 1]}/A1", hops[i]))
    return links


def test_chain_link_costs_prices_a_link_with_its_routed_hop():
    edges = defaultdict(list)
    chains = {
        "uut.ux.udly": add_chain(edges, "uut.ux.udly", [124, 124, 124],
                                 [400, 440]),
        "uut.uy.udly": add_chain(edges, "uut.uy.udly", [124], []),
    }
    costs = tighten.chain_link_costs(edges, chains)
    # n LUT arcs and n - 1 hops: one more link is a LUT plus a hop, 544 ps on
    # average -- not the chain's 1212 ps / 3 = 404, and a one-link chain has
    # no hop to measure, so it is not priced from itself at all.
    assert costs == {"uut.ux.udly": 544}


# xorshift it1 seed 1, ucontrol_merge1: 1 link (124 ps, the LUT arc alone),
# margin -3162 ps with the guardband applied.  The cheapest link on that route
# cost 419 ps (LUT + hop).  The old pricing divided the chain by n, 124 ps a
# link, and asked for 27; the routes at 32 links then said 2-5.
def test_rule_a_pad_without_own_hop_uses_cheapest_link_on_route():
    want, per, how = tighten.rule_a_links(1, -3162, None, [419, 455, 700], 124)
    assert (want, per) == (9, 419)
    assert how == "route minimum"
    # and it still pads enough: the added links cover the deficit at the
    # cheapest per-link cost the route showed
    assert (want - 1) * per >= 3162


def test_rule_a_pad_uses_own_chain_when_it_has_a_hop():
    # uxori2, it1 seed 4: 3 links, 1106 ps, own marginal 491 ps; old said 7.
    assert tighten.rule_a_links(3, -1163, 491, [419, 491, 700], 1106 / 3)[0] == 6


def test_rule_a_tighten_never_removes_more_than_the_margin_covers():
    # uxori1, it1 seed 1: 3 links, margin 425, one link costs 489 here.  Old
    # pricing (1102 / 3 = 367 ps) removed one and left the request 64 ps short.
    assert tighten.rule_a_links(3, 425, 489, [419, 489, 700], 1102 / 3)[0] == 3
    # Without its own hop, a tighten is priced at the DEAREST link: umux3,
    # 1 link, margin 148 -- the old 124 ps price dropped it to 0.
    assert tighten.rule_a_links(1, 148, None, [419, 700], 124)[:2] == (1, 700)
    # A margin that really covers the dearest link does tighten.
    assert tighten.rule_a_links(1, 701, None, [419, 700], 124)[0] == 0


def test_rule_a_without_any_chain_on_route_falls_back():
    assert tighten.rule_a_links(0, -413, None, [], 300) == (
        2, 300, "no chain on this route to measure")
