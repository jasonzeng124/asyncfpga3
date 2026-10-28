#!/usr/bin/env python3
"""Gate for bdc/slack.py.

Two kinds of case, deliberately kept separate:

  Synthetic (test_scc_gap_*, test_tokens_*): small hand-written handshake.func
  snippets that isolate ONE property of the algorithm each -- in particular
  the SCC-decomposition gap the slack.py module docstring names explicitly
  (an SCC containing a storage node does not prove every simple cycle inside
  it does) -- and prove the two-round Tarjan construction actually closes it,
  not just that it happens to agree on the real corpus.

  Real corpus (test_kernel_*): the four compiled kernels named in the task
  brief, at build/frontend/*/comp/handshake_transformed.mlir. Every number
  asserted there was measured by running slack.py against the file, not
  guessed -- see the bdc/slack.py --report run this file's numbers came from.
  Per the brief: a kernel failing the cycle check is a RESULT, not a bug to
  paper over, because none of these four kernels contain a `buffer` op
  (bd-config.json's own corpus count says so: "seen": 0) and this backend
  never runs --handshake-place-buffers, the pass that would normally have put
  one there. single_loop, fir and gcd are therefore EXPECTED to fail the
  cycle check today; asserting that failure is the point of these tests, not
  a bug in slack.py. test_loop_free has no loop at all and is the vacuous
  base case the brief asks for explicitly.

Run:  python3 bdc/test_slack.py
"""

import glob
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from hs import parse  # noqa: E402
import slack  # noqa: E402


class TestStorageOps(unittest.TestCase):
    def test_only_buffer_provides_storage(self):
        """Grounded in bd-config.json's own `cells` lists (see slack.py's
        storage_ops()), not hardcoded. Today exactly one op maps to a cell
        that holds a token across a transaction boundary: `buffer`, via
        bd_link/bd_pipe's bd_latch. If this ever changes -- a new op gets
        mapped onto bd_link/bd_pipe, or `buffer` stops being -- that is
        exactly the kind of change bdc/AUDIT.md exists to record, and this
        test existing is what forces that conversation to happen instead of
        silently changing what counts as a hard error."""
        self.assertEqual(slack.storage_ops(), {"buffer"})


class TestTarjanSCC(unittest.TestCase):
    """Direct tests of the graph primitive, independent of the MLIR reader."""

    def test_acyclic_chain_has_no_nontrivial_scc(self):
        adj = {0: {1}, 1: {2}, 2: set()}
        sccs = slack.tarjan_scc([0, 1, 2], adj)
        cycles = [c for c in sccs if slack._is_cycle(c, adj)]
        self.assertEqual(cycles, [])

    def test_two_node_cycle_is_one_scc(self):
        adj = {0: {1}, 1: {0}}
        sccs = slack.tarjan_scc([0, 1], adj)
        cycles = [c for c in sccs if slack._is_cycle(c, adj)]
        self.assertEqual(len(cycles), 1)
        self.assertEqual(set(cycles[0]), {0, 1})

    def test_self_loop_is_a_cycle_but_lone_node_is_not(self):
        adj = {0: {0}, 1: set()}
        sccs = slack.tarjan_scc([0, 1], adj)
        by_size = sorted(sccs, key=len)
        self.assertTrue(slack._is_cycle([0], adj))
        self.assertFalse(slack._is_cycle([1], adj))

    def test_restricting_node_set_deletes_edges_through_removed_nodes(self):
        """This is the exact mechanism Round 2 of check_cycles relies on:
        deleting a node from the id set passed to tarjan_scc removes every
        edge touching it, even though `adj` itself is untouched."""
        adj = {0: {1}, 1: {2}, 2: {0}}
        full = [c for c in slack.tarjan_scc([0, 1, 2], adj) if slack._is_cycle(c, adj)]
        self.assertEqual(len(full), 1)
        residual = [c for c in slack.tarjan_scc([0, 2], adj) if slack._is_cycle(c, adj)]
        self.assertEqual(residual, [])  # removing node 1 breaks the only cycle


class TestSCCGapIsClosed(unittest.TestCase):
    """The counterexample from slack.py's own docstring, built as real
    (if tiny) handshake IR and run through the real parser and the real
    check_cycles -- not just the graph primitive in isolation.

    Shape: node Ain merges two back-edges (from B, and from D) and forks out
    to Aout, which drives both B and C. B closes DIRECTLY back to Ain -- no
    storage on that path. C goes through D (a `buffer`, i.e. real storage)
    before closing back to Ain. Ain/Aout/B/C/D therefore form ONE Tarjan SCC
    that DOES contain a storage node (D) -- so a checker that only asked "does
    this SCC contain a storage node anywhere" would call the whole thing
    clear. The A-B sub-cycle would still be a real, unbuffered combinational
    loop. This is exactly the A/B/C/D example in slack.py's module docstring.
    """

    GAP_TEXT = """
handshake.func @gap_demo(%arg0: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["start"], resNames = ["out"]} {
  %ain = merge %b, %d {handshake.name = "Ain"} : <>
  %aout:2 = fork [2] %ain {handshake.name = "Aout"} : <>
  %b = br %aout#0 {handshake.name = "B"} : <>
  %c = br %aout#1 {handshake.name = "C"} : <>
  %d = buffer %c, bufferType = ONE_SLOT_BREAK_DV, numSlots = 1, dvLatency = 1 {handshake.name = "D"} : <>
  end {handshake.name = "end0"} %arg0 : <>
}
"""

    # Positive control: same shape, but the ONLY cycle present is routed
    # through the buffer -- so with no unbuffered sub-cycle left, this one
    # must come back clean. Confirms storage is actually recognised, not
    # that check_cycles simply flags everything.
    OK_TEXT = """
handshake.func @loop_with_buffer(%arg0: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["start"], resNames = ["out"]} {
  %m = merge %arg0, %d {handshake.name = "M"} : <>
  %b = br %m {handshake.name = "B"} : <>
  %d = buffer %b, bufferType = ONE_SLOT_BREAK_DV, numSlots = 1, dvLatency = 1 {handshake.name = "D"} : <>
  end {handshake.name = "end0"} %d : <>
}
"""

    def test_round1_alone_would_be_fooled(self):
        func = parse.parse_func(self.GAP_TEXT)
        report = slack.check_cycles(func)
        # One merged SCC, and it DOES contain a storage node (D) -- this is
        # precisely the state a naive "storage somewhere in the SCC" check
        # would call passing.
        self.assertEqual(report.n_sccs, 1)
        self.assertEqual(report.n_storage_backed, 1)

    def test_round2_still_catches_the_unbuffered_subcycle(self):
        func = parse.parse_func(self.GAP_TEXT)
        report = slack.check_cycles(func)
        self.assertEqual(len(report.violations), 1)
        # The surviving violation is exactly the {Ain, Aout, B} sub-cycle --
        # C and D are not in it, because C's only outgoing edge (to D, the
        # storage node) is exactly what got deleted for Round 2.
        got = {label.split(" (")[0] for label in report.violations[0].node_labels}
        self.assertEqual(got, {"Ain", "Aout", "B"})
        # And the reported channels are real edges of that sub-cycle, usable
        # as bd_link insertion points -- not an empty or unrelated list.
        edge_pairs = {(p.split(" (")[0], c.split(" (")[0])
                      for p, c, _val in report.violations[0].channels}
        self.assertEqual(edge_pairs, {("Ain", "Aout"), ("Aout", "B"), ("B", "Ain")})

    def test_fully_buffered_cycle_has_no_violation(self):
        func = parse.parse_func(self.OK_TEXT)
        report = slack.check_cycles(func)
        self.assertEqual(report.n_sccs, 1)
        self.assertEqual(report.n_storage_backed, 1)
        self.assertEqual(report.violations, [])


class TestTokenConservation(unittest.TestCase):
    def test_double_use_without_a_fork_is_a_violation(self):
        text = """
handshake.func @double_use(%arg0: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["start"], resNames = ["out"]} {
  sink %arg0 {handshake.name = "SNK0"} : <>
  %s = source {handshake.name = "S"} : <>
  %b0 = br %s {handshake.name = "B0"} : <>
  %b1 = br %s {handshake.name = "B1"} : <>
  sink %b1 {handshake.name = "SNK1"} : <>
  end {handshake.name = "end0"} %b0 : <>
}
"""
        func = parse.parse_func(text)
        report = slack.check_tokens(func)
        self.assertEqual(len(report.violations), 1)
        self.assertEqual(report.violations[0].value, "s")
        self.assertEqual(report.violations[0].n_consumers, 2)

    def test_unconsumed_value_is_a_violation(self):
        text = """
handshake.func @unconsumed(%arg0: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["start"], resNames = ["out"]} {
  %s = source {handshake.name = "S"} : <>
  %c = constant %s {handshake.name = "C", value = 0 : i32} : <>, <i32>
  end {handshake.name = "end0"} %arg0 : <>
}
"""
        func = parse.parse_func(text)
        report = slack.check_tokens(func)
        self.assertEqual(len(report.violations), 1)
        self.assertEqual(report.violations[0].value, "c")
        self.assertEqual(report.violations[0].n_consumers, 0)

    def test_materialized_graph_is_clean(self):
        """A value used exactly once, and a fork whose results are each used
        exactly once, are both fine -- this is the common case in every real
        kernel below, asserted directly here so a regression has a minimal
        reproduction instead of only failing 200 lines into a real kernel."""
        text = """
handshake.func @clean(%arg0: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["start"], resNames = ["out"]} {
  %f:2 = fork [2] %arg0 {handshake.name = "F"} : <>
  %b0 = br %f#0 {handshake.name = "B0"} : <>
  sink %b0 {handshake.name = "SNK0"} : <>
  end {handshake.name = "end0"} %f#1 : <>
}
"""
        func = parse.parse_func(text)
        report = slack.check_tokens(func)
        self.assertEqual(report.violations, [])


# ---------------------------------------------------------------------------
# The real corpus.

CORPUS_ROOT = os.path.join(ROOT, "build", "frontend")


def _load(kernel):
    path = os.path.join(CORPUS_ROOT, kernel, "comp", "handshake_transformed.mlir")
    if not os.path.exists(path):
        raise unittest.SkipTest(
            f"{path} not built -- run bdc/frontend.sh {kernel} first")
    with open(path) as fh:
        funcs = parse.parse_module(fh.read(), filename=path)
    bodies = [f for f in funcs if not f.is_declaration]
    assert len(bodies) == 1, f"expected exactly one defined handshake.func in {path}"
    return bodies[0]


class TestRealKernels(unittest.TestCase):
    """Numbers measured by running slack.py against the four kernels named in
    the task brief. Every assertion below is the actual observed count, not
    an estimate -- see this file's own module docstring."""

    def test_test_loop_free_is_the_vacuous_base_case(self):
        """No back-edge in the source at all (straight-line if/else, no
        loop), so the cycle obligation is vacuously satisfied: zero SCCs,
        zero violations, nothing to buffer. This is the case the task brief
        asks to confirm explicitly."""
        func = _load("test_loop_free")
        cyc = slack.check_cycles(func)
        tok = slack.check_tokens(func)
        self.assertEqual(cyc.n_nodes, 39)
        self.assertEqual(cyc.n_sccs, 0)
        self.assertEqual(cyc.n_storage_backed, 0)
        self.assertEqual(cyc.violations, [])
        self.assertEqual(tok.n_values, 53)
        self.assertEqual(tok.violations, [])

    def test_single_loop_has_one_merged_unbuffered_cycle(self):
        """The first kernel with a real loop. Its two memory accesses and its
        loop-carried induction variable all end up in ONE Tarjan SCC (they
        share a fork on the loop's control token, fork1/fork5 in the actual
        graph), not three separate ones -- a real structural fact about this
        kernel, not a modelling choice. No `buffer` op exists anywhere in the
        file (bd-config.json's own corpus count agrees: "seen": 0 for
        `buffer`), so this is correctly reported as a hard error: the
        compiler has not placed the storage stage COMPILER-PLAN Stage 5 says
        it owns. Token conservation holds -- --handshake-materialize already
        ran when this file was produced (see bdc/frontend.sh step 8)."""
        func = _load("single_loop")
        cyc = slack.check_cycles(func)
        tok = slack.check_tokens(func)
        self.assertEqual(cyc.n_nodes, 35)
        self.assertEqual(cyc.n_sccs, 1)
        self.assertEqual(cyc.n_storage_backed, 0)
        self.assertEqual(len(cyc.violations), 1)
        self.assertGreater(len(cyc.violations[0].channels), 0)
        self.assertEqual(tok.n_values, 58)
        self.assertEqual(tok.violations, [])

    def test_fir_has_four_separate_unbuffered_cycles(self):
        """Unlike single_loop, fir's two mem_controllers do NOT share a fork,
        so each one's own address/data round trip is its own separate SCC;
        together with the induction-variable loop and the accumulator loop
        that is four SCCs total, all storage-free for the same reason as
        single_loop (no `buffer` op in the file)."""
        func = _load("fir")
        cyc = slack.check_cycles(func)
        tok = slack.check_tokens(func)
        self.assertEqual(cyc.n_nodes, 40)
        self.assertEqual(cyc.n_sccs, 4)
        self.assertEqual(cyc.n_storage_backed, 0)
        self.assertEqual(len(cyc.violations), 4)
        self.assertEqual(tok.n_values, 61)
        self.assertEqual(tok.violations, [])

    def test_gcd_has_ten_separate_unbuffered_cycles(self):
        """gcd is the largest kernel (239 nodes, 13 basic blocks) and the one
        with the 3-way mux/control_merge tree bd-config.json calls out. Ten
        distinct SCCs, one per loop-carried variable's own back-edge (most of
        gcd's basic blocks pass several live variables through unchanged,
        each getting its own merge/mux pair and its own short cycle), all
        storage-free for the same reason as the other two loop kernels."""
        func = _load("gcd")
        cyc = slack.check_cycles(func)
        tok = slack.check_tokens(func)
        self.assertEqual(cyc.n_nodes, 239)
        self.assertEqual(cyc.n_sccs, 10)
        self.assertEqual(cyc.n_storage_backed, 0)
        self.assertEqual(len(cyc.violations), 10)
        self.assertEqual(tok.n_values, 354)
        self.assertEqual(tok.violations, [])


if __name__ == "__main__":
    unittest.main()
