from collections import defaultdict
import sys

sys.path.insert(0, str(__file__).rsplit("/", 2)[0])
import tighten


def chain_edges(side_arcs):
    edges = defaultdict(list)
    source = "uor/O6"
    for i in range(4):
        inst = f"delay.chain.g[{i}].u"
        input_pin = f"{inst}/I0"
        output_pin = f"{inst}/O6"
        edges[source if i == 0 else
              f"delay.chain.g[{i - 1}].u/O6"].append((input_pin, 10))
        edges[input_pin].append((output_pin, 10))
        if side_arcs and i > 0:
            edges[source].append((f"{inst}/I1", 1))
            edges[f"{inst}/I1"].append((output_pin, 10))
    return edges


def test_fastfall_side_arcs_are_excluded_from_early_arrivals():
    edges = chain_edges(side_arcs=True)
    side = tighten.fastfall_side_arcs(edges)
    timing = tighten.Timing(edges, set())
    target = "delay.chain.g[3].u/O6"

    assert ("uor/O6", "delay.chain.g[3].u/I1") in side
    assert ("delay.chain.g[2].u/O6", "delay.chain.g[3].u/I0") not in side
    assert timing.early("uor/O6")[target] == 80
    assert timing.late("uor/O6")[target] == 80


def test_lut1_chain_has_no_fastfall_side_arcs():
    assert tighten.fastfall_side_arcs(chain_edges(side_arcs=False)) == set()


# ----------------------------------------------------- rule F: the drain

def drained_line(side1, ret):
    """c (a link's node) -> 3-link FASTFALL rdly -> consumer k -> back to c.
    Ripple wires 1000 ps, side taps 10 ps except into g[1] (side1); the
    return path from the tail to c costs `ret`."""
    edges = defaultdict(list)
    src = "l.ctl.u.u/O6"
    base = "l.rdly"
    prev = src
    for i in range(3):
        inst = f"{base}.chain.g[{i}].u"
        edges[prev].append((f"{inst}/I0", 10 if i == 0 else 1000))
        edges[f"{inst}/I0"].append((f"{inst}/O6", 10))
        if i > 0:
            edges[src].append((f"{inst}/I1", side1 if i == 1 else 10))
            edges[f"{inst}/I1"].append((f"{inst}/O6", 10))
        prev = f"{inst}/O6"
    edges[prev].append(("k.u/I0", ret // 2))
    edges["k.u/I0"].append(("k.u/O6", 10))
    edges["k.u/O6"].append(("l.ctl.u.u/I1", ret // 2 - 20))
    edges["l.ctl.u.u/I1"].append((src, 10))
    back = defaultdict(set)
    for s, lst in edges.items():
        for d, _ in lst:
            back[d].add(s)
    chains = tighten.find_chains(edges)
    timing = tighten.Timing(edges, {src, "k.u/O6"})
    return tighten.audit_fastfall(edges, back, chains, timing)


def test_rule_f_passes_a_line_that_drains_with_its_tail():
    (row,) = drained_line(side1=10, ret=400)
    base, n, t_flush, t_reuse, guard, margin = row
    assert base == "l.rdly" and n == 3
    assert t_flush == 20 and margin > 0


def test_rule_f_fails_a_stage_that_is_still_high_when_the_input_returns():
    # g[1]'s side tap is 2 ns late and the ripple is slower still: it falls
    # at 1030, long after the tail (20) and the return (400) let c rise again.
    (row,) = drained_line(side1=2000, ret=400)
    margin = row[-1]
    assert row[2] == 1030 and margin < 0
