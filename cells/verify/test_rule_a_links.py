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
