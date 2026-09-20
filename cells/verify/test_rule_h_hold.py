from collections import defaultdict
import sys

sys.path.insert(0, str(__file__).rsplit("/", 2)[0])
import tighten


def graph(arcs):
    edges = defaultdict(list)
    back = defaultdict(set)
    for src, dst, d in arcs:
        edges[src].append((dst, d))
        back[dst].add(src)
    return edges, back


def two_links():
    """sender ctl -> sender latch -> xor -> receiver latch; receiver ctl acks
    the sender through a two-stage uack chain and drives two latch enables
    with very different routes."""
    arcs = [
        # receiver controller: enables (skewed) and its acknowledge chain
        ("rx.ctl.u.u/O6", "rx.lat.pair[0].u$LUT5/I1", 150),
        ("rx.lat.pair[0].u$LUT5/I1", "rx.lat.pair[0].u$LUT5/O5", 120),
        ("rx.ctl.u.u/O6", "rx.lat.pair[1].u$LUT5/I1", 1100),
        ("rx.lat.pair[1].u$LUT5/I1", "rx.lat.pair[1].u$LUT5/O5", 120),
        ("rx.ctl.u.u/O6", "rx.uack.chain.g[0].u/I0", 100),
        ("rx.uack.chain.g[0].u/I0", "rx.uack.chain.g[0].u/O6", 120),
        ("rx.uack.chain.g[0].u/O6", "rx.uack.chain.g[1].u/I0", 100),
        ("rx.uack.chain.g[1].u/I0", "rx.uack.chain.g[1].u/O6", 120),
        # FASTRISE side arc into stage 1: must not shorten the fall
        ("rx.ctl.u.u/O6", "rx.uack.chain.g[1].u/I1", 100),
        ("rx.uack.chain.g[1].u/I1", "rx.uack.chain.g[1].u/O6", 120),
        # the acknowledge reaches the sender's controller
        ("rx.uack.chain.g[1].u/O6", "tx.ctl.u.u/I3", 300),
        ("tx.ctl.u.u/I3", "tx.ctl.u.u/O6", 120),
        # sender controller opens its latch; latch feeds xor feeds receiver
        ("tx.ctl.u.u/O6", "tx.lat.pair[0].u$LUT5/I1", 200),
        ("tx.lat.pair[0].u$LUT5/I1", "tx.lat.pair[0].u$LUT5/O5", 120),
        ("tx.lat.pair[0].u$LUT5/O5", "xor.u/I0", 250),
        ("xor.u/I0", "xor.u/O6", 120),
        ("xor.u/O6", "rx.lat.pair[0].u$LUT5/I0", 250),
        ("xor.u/O6", "rx.lat.pair[1].u$LUT5/I0", 250),
        # receiver latch feedback
        ("rx.lat.pair[0].u$LUT5/O5", "rx.lat.pair[0].u$LUT5/I2", 50),
        ("rx.lat.pair[1].u$LUT5/O5", "rx.lat.pair[1].u$LUT5/I2", 50),
    ]
    edges, back = graph(arcs)
    stops = {"rx.ctl.u.u/O6", "tx.ctl.u.u/O6", "tx.lat.pair[0].u$LUT5/O5",
             "rx.lat.pair[0].u$LUT5/O5", "rx.lat.pair[1].u$LUT5/O5"}
    return edges, back, stops


def test_latch_enables_and_data_pins():
    edges, back, _ = two_links()
    enables = tighten.latch_enables(edges, "rx.ctl.u.u/O6")
    assert sorted(enables) == [("rx.lat.pair[0].u$LUT5/I1", 150),
                               ("rx.lat.pair[1].u$LUT5/I1", 1100)]
    en_pins = {p for p, _ in enables}
    insts = {tighten.pin_split(p)[0] for p in en_pins}
    assert tighten.latch_data_pins(back, insts, en_pins) == {
        "rx.lat.pair[0].u$LUT5/I0", "rx.lat.pair[1].u$LUT5/I0"}
    assert tighten.latch_enables(edges, "tx.lat.pair[0].u$LUT5/O5") == []


def test_disturbance_crosses_storage_but_not_own_latches():
    edges, back, stops = two_links()
    timing = tighten.Timing(edges, stops)
    targets = {"rx.lat.pair[0].u$LUT5/I0", "rx.lat.pair[1].u$LUT5/I0"}
    own = lambda p: tighten.pin_split(p)[0].startswith("rx.lat.")
    hit, reached = tighten.earliest_disturbance(
        timing, "rx.ctl.u.u/O6", targets, own)
    # fall through both chain stages (side arc excluded), then the sender
    # controller, latch, xor: 100+120+100+120+300+120+200+120+250+120+250
    assert hit == 1800
    assert "tx.ctl.u.u/O6" in reached and "tx.lat.pair[0].u$LUT5/O5" in reached
    assert not any(own(p) for p in reached)


def test_fastrise_side_arc_carries_the_rise_only():
    edges, back, stops = two_links()
    timing = tighten.Timing(edges, stops)
    out = "rx.uack.chain.g[1].u/O6"
    assert timing.early_fall("rx.ctl.u.u/O6", "rx")[out] == 440
    assert timing.early("rx.ctl.u.u/O6", "rx")[out] == 220
    assert timing.early_any("rx.ctl.u.u/O6", "rx")[out] == 220
    assert timing.late("rx.ctl.u.u/O6", "rx")[out] == 440
    assert tighten.fastrise_side_arcs(edges) == {
        ("rx.ctl.u.u/O6", "rx.uack.chain.g[1].u/I1")}
    assert tighten.fastfall_side_arcs(edges) == set()


def test_stage_delay_knob():
    knob = tighten.stage_delay_knob
    pipe = "uut.ulink_x.many.stage[%d].u.ctl.u.u/O6"
    assert knob(pipe % 1, pipe % 2) == \
        ("uut.ulink_x.sdelay", "uut.ulink_x.many.stage[1].u.rdly")
    assert knob(pipe % 3, "uut.ulink_y.ctl.u.u/O6") == \
        ("uut.ulink_x", "uut.ulink_x.many.stage[3].u.rdly")
    assert knob("uut.ulink_y.one.u.ctl.u.u/O6", pipe % 0) == \
        ("uut.ulink_y", "uut.ulink_y.one.u.rdly")
    assert knob("uut.ulink_y.ctl.u.u/O6", pipe % 0) == \
        ("uut.ulink_y", "uut.ulink_y.rdly")
    assert knob("uut.ucomp.uor.u/O6", pipe % 0) is None
