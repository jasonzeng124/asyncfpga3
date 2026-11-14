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


def test_chain_link_costs_ignores_a_side_tap_the_step_does_not_use():
    # A FASTRISE/FASTFALL line: every stage past the first also hears the
    # line's input on a side pin.  The step from link i to link i+1 enters on
    # the pin link i drives, so that pin's LUT arc is the one an added link
    # costs -- not a cheaper arc from the side tap.
    edges = defaultdict(list)
    links = add_chain(edges, "uut.ul.uack", [124, 124, 124], [400, 440])
    for link in links[1:]:
        edges["drv/O6"].append((f"{link}/A2", 900))
        edges[f"{link}/A2"].append((f"{link}/O6", 50))
    costs = tighten.chain_link_costs(edges, {"uut.ul.uack": links})
    assert costs == {"uut.ul.uack": 544}


# Rules H, B and C size a bd_delay line by the same arithmetic as rule A.  Each
# used to divide a measured span by n; each span holds more than the link-to-
# link steps an added link repeats.  Numbers below are a line of LUT 124 ps
# and hop 300 ps: one more link is 424 ps.

def test_rule_h_pads_at_the_line_own_link_cost():
    # 3-link uack line, 600 ps from the node into it: t_exit = 600 + 3*124 +
    # 2*300 = 1572, and t_exit / 3 = 524 ps a link.  Margin -500 needs two
    # links at 424; the old price asked for one, 76 ps short.
    want, per, how = tighten.rule_h_links(3, -500, 424, [419, 424, 700],
                                          1572, 274)
    assert (want, per, how) == (5, 424, "own chain")
    assert (want - 3) * per >= 500


def test_rule_h_tighten_without_own_hop_never_beats_the_old_price():
    # 1-link line: no hop of its own.  Priced at the dearer of the route's
    # dearest link and the old t_exit / n, so it never removes more than the
    # old price did.
    assert tighten.rule_h_links(1, 1000, None, [419, 700], 1100, 274)[:2] == (
        1, 1100)
    assert tighten.rule_h_links(1, 1200, None, [419, 700], 1100, 274)[0] == 0


def test_rule_h_tighten_with_own_hop_keeps_the_hop_into_the_line():
    # gcd_hw wtR2g_s2, ulink_n8__1 stage 1: 2-link uack line, one step 419 ps,
    # margin 1575.  Taking the line to 0 also removes the hop from the node
    # into it, which t_exit carries (here > 1575: the old price said 1).
    # Priced at the step alone it went to 0.
    assert tighten.rule_h_links(2, 1575, 419, [419, 700], 1600, 274)[:2] == (
        1, 800)


def test_rule_b_tightens_no_further_than_the_link_it_removes():
    # 2-link usetup line, 2*124 + 300 = 548 ps, so chain / n = 274.  Margin
    # 300 cannot pay for a 424 ps link; the old price removed it anyway.
    assert tighten.rule_b_links(2, 300, 424, [424], 548, 300)[0] == 2
    assert tighten.rule_b_links(2, 430, 424, [424], 548, 300)[0] == 1


def test_rule_c_tightens_no_further_than_the_link_it_removes():
    # 9-link uco line fed off the RAM's clock net: best = 9*124 + 8*300 =
    # 3516, best / 9 = 391 ps a link.  Margin 400 cannot pay for a 424 ps
    # link; the old price removed one anyway.
    assert tighten.rule_c_links(9, 400, 424, [424], 3516)[:2] == (9, 424)
    assert tighten.rule_c_links(9, 424, 424, [424], 3516)[0] == 8
    # and it keeps one link, however large the margin
    assert tighten.rule_c_links(2, 10_000, 424, [424], 1300)[0] == 1
