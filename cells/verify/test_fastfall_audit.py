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
