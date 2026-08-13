#!/usr/bin/env python3
"""Phase 4 / COMPILER-PLAN Stage 5: slack, in place of Dynamatic's buffer
placement.

Dynamatic places buffers with a MILP that optimises against a clock period.
There is no clock here, so that formulation has nothing to optimise against
-- COMPILER-PLAN.md deliberately does not run `--handshake-place-buffers`
and cuts the pipeline immediately above it. But that pass was not doing only
throughput. Buried inside "optimise placement" is a correctness precondition
every solution it emits happens to satisfy: every cycle in the dataflow graph
gets at least one buffer. Skip the pass and that precondition goes unchecked,
not just unoptimised. This module is what re-imposes it, split into exactly
the three obligations COMPILER-PLAN Stage 4/5 names:

  1. cycle check       -- every cycle must contain >=1 storage-providing node
  2. token conservation -- every produced value has exactly one consumer
  3. insertion reporting -- WHERE a bd_link would fix a cycle check failure

THROUGHPUT IS NOT MODELLED HERE, ON PURPOSE. A four-phase pipe's cycle is a
full round trip and the simple controller holds one token per two stages;
adding storage costs area and latency and buys concurrency. With no clock to
meet, that is a pure trade with no objective function to optimise against --
so COMPILER-PLAN says measure it on hardware, not model it, and this module
holds that line. It answers "does this design work at all", never "is this
design fast enough" -- there is no "fast enough" without a clock to be fast
enough for.

-- which nodes provide STORAGE, and how that was decided -----------------

"Storage" here means: a node whose data-holding element persists across a
full handshake transaction, independent of what its neighbours are doing at
that instant -- the property that lets one side of a cycle sit still while
the graph closes the loop around it, and the reason a cycle with no such node
cannot be phased at all (its own request would have to settle against itself
in zero elements).

Grounded in cells/rtl/, not assumed:

  bd_link / bd_pipe (rtl/bd_link.v) ARE storage. Their `bd_latch` (defined in
  rtl/bd_latch.v, whose own header opens with "Storage without a clock edge")
  is a transparent latch that CLOSES at ack-fall and stays closed, holding
  the datum, until the stage's own next req-rise -- entirely independent of
  what the neighbouring stages are doing meanwhile. `bd-config.json` maps
  exactly one handshake op to these cells: `buffer`.

  fork / join (rtl/bd_ctl.v, via bd_ctree in rtl/bd_ce.v) do NOT count,
  despite containing C-elements (Muller gates), which are real bistable
  circuits with feedback and a `rst` pin, same as the ones inside bd_link.
  This is the judgement call the task brief asked to check for, and the
  evidence against it is in bd_ctree's own header: "every sub-tree returns
  to zero every cycle and can never be stale" -- i.e. these C-elements
  resolve ONE transaction's rendezvous and then reset; they hold no token
  independent of the transaction currently in flight, so there is nothing
  for a second, concurrent transaction to rest on. bd_steer (also in
  bd_ctl.v) makes the same point from the opposite direction: it needs no
  C-element and has none ("No feedback wire, so no keep attribute, no loop
  ... and no reset") and is obviously not storage, yet it is built to the
  same "route the handshake, do not hold it" contract as fork/join.

  mux / arbiter (rtl/bd_mux.v, rtl/bd_arb.v) do NOT count either, for the
  same reason plus one more: bd_mux's datapath (`bd_datamux`, rtl/bd_latch.v)
  is stated to be plain combinational muxing, and its C-elements (`j0`/`j1`,
  the acks) are per-transaction rendezvous exactly like fork/join's. The
  arbiter's state node (`bd_c2n_set` in bd_arbcell) IS long-lived -- it
  remembers which client won last, across many transactions, unlike
  bd_ctree's -- but what it remembers is a PRIORITY BIT for fairness, not a
  data token; it does not let one side of a data cycle sit at rest while the
  other advances, which is the property this check needs. See
  bdc/AUDIT.md section 6, added by this module's author, for the full
  writeup of this finding.

  load / store / mem_controller (rtl/bd_mem.v) are NOT counted as storage
  by this checker, despite bd_mem instantiating a real clocked RAMB18E1 --
  the strongest storage element in the library, stronger than a latch.
  The reason is not the RTL, it is the table: bd-config.json marks all
  three `"kind": "todo"` with no committed `"cells"` entry (Stage 6 is
  unbuilt), and bdc/AUDIT.md section 2 already states that none of
  Dynamatic's cycle-level memory guarantees are safe to assume here without
  their own audit entry. Crediting an unaudited, unbuilt op with a
  correctness-relevant property is exactly the mistake AUDIT.md exists to
  prevent ("An op mapping that is not written down here has not been
  audited and must not be assumed safe"). Concretely, this means a cycle
  that only closes through a mem_controller's own address/data round trip
  (mem_controller -> load -> mem_controller, the address echo) is reported
  as a violation by this checker today. That is flagged in this module's
  test output as an open question for Stage 6, not silently special-cased
  away.

Concretely: STORAGE_OPS is computed from bd-config.json's own `"cells"`
lists (any op whose cells intersect {bd_link, bd_pipe}), not hardcoded --
so this module and bdc/map.py can never disagree about what `buffer` means.

-- cycle enumeration: SCC decomposition, not Johnson's algorithm ----------

The task allows either. Johnson's algorithm enumerates every simple cycle
and is exponential in the worst case; nothing in a compiled dataflow graph
needs that much detail; SCC decomposition is linear and is what this module
uses, in two rounds:

  Round 1 (diagnostic).  Tarjan's algorithm on the full node graph gives
  every non-trivial SCC (size > 1, or a size-1 SCC with a self-loop -- a
  single node whose own result feeds back into itself). Report how many
  there are and how many contain at least one storage node. This number is
  informative but NOT the correctness verdict: an SCC containing a storage
  node somewhere does not, by itself, prove every simple cycle inside that
  SCC passes through it. A textbook counterexample: nodes A, B, C, D with
  edges A->B->A and A->C->D->A share node A but are different cycles: if D
  is the only storage node, the first cycle (A->B->A) still has none, yet a
  "does this SCC contain a storage node" check would call the whole SCC
  clear.

  Round 2 (the actual verdict).  Delete every storage node from the graph
  entirely (not just from one SCC) and re-run Tarjan's on what is left. Any
  non-trivial SCC that survives is, by construction, a cycle that visits
  NO storage node anywhere -- because every node in it is, by definition of
  the node set being decomposed, a non-storage node. This closes the gap
  Round 1 leaves open, stays linear (two Tarjan passes, not exponential
  enumeration), and needs no per-cycle bookkeeping: "is the graph, minus the
  nodes that provide storage, still cyclic" is exactly the question "does
  some cycle avoid every storage node", answered without ever naming a
  cycle explicitly. Round 2's violations are what `check_cycles` reports as
  hard errors and what `suggest_insertions` reports channels for.

  For the four kernels this module is gated against, no `buffer` op appears
  at all (bd-config.json records `"seen": 0`), so the storage-node set is
  always empty and Round 1 and Round 2 agree trivially. The A/B/C/D gap
  above is therefore not exercised by this corpus; it is closed anyway,
  because closing it costs nothing extra (one more linear pass) and a
  compiler that inserts bd_link stages in later work could easily produce
  exactly that shared-skeleton shape (several loop-carried variables through
  one loop header, only some of them buffered).

-- token conservation -------------------------------------------------------

`--handshake-materialize` (see bdc/AUDIT.md section 5, and its own pass
description) guarantees every SSA value in a handshake.func is used EXACTLY
once, by inserting `fork` where a value had multiple uses and `sink` where
it had none. That is already the one-producer/one-consumer discipline this
check needs; nothing here re-derives it, this module only VERIFIES the
guarantee actually held on the file it was given. Concretely: for every
value a node or a function argument produces, count its consumers via
Func.consumers (parse.py already resolved every operand reference to a
producer at parse time, so an operand referring to nothing is already a
ParseError, not something this module has to detect). Zero consumers or two
or more are both violations, and both get reported by name rather than
merged into one "wrong count" bucket, because they point at different bugs:
zero means either the frontend emitted a value nothing was told to consume
(materialize should have inserted a sink and did not) or this reader failed
to see a real consumer (a bug in parse.py, or in this module's operand
walk); two-or-more means either materialize's fork insertion did not run,
or this reader double-counted one physical use as two references. Both are
worth failing loudly on, per the task brief -- this module states which
shape of anomaly it saw and lets a human decide which side of the boundary
is actually wrong, rather than guessing.

`fork` producing N results from 1 operand is not a violation of anything --
each of its N results is its OWN distinct SSA value with its own single
consumer, so the generic "exactly one consumer per produced value" rule
already covers fan-out correctly with no fork-shaped special case. The same
is true of every other op the task brief calls out (`sink`, `cond_br`,
`mux`, `control_merge`): none of them need bespoke conservation logic,
because materialize already normalised the graph down to values with a
single well-defined producer and (if the graph is healthy) a single
consumer, and that is the only invariant this module checks.
"""

import argparse
import os
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hs import parse  # noqa: E402
from map import Table  # noqa: E402

# Cells whose data-holding element (a latch, or -- once Stage 6 is audited --
# a clocked memory) persists across a full transaction, independent of
# neighbouring handshake state. See the module docstring for why the
# rendezvous C-elements inside fork/join/mux/arbiter do NOT belong here even
# though they are real bistable circuits.
STORAGE_CELLS = frozenset({"bd_link", "bd_pipe"})


def storage_ops(table=None):
    """The set of handshake op names that provide storage, derived from
    bd-config.json's own `cells` lists rather than hardcoded -- so this
    module and bdc/map.py can never quietly disagree about what a `buffer`
    lowers to. An op qualifies if ANY of its guarded entries names a cell in
    STORAGE_CELLS; today that is `buffer` alone (guard-free, cells:
    [bd_link, bd_pipe]) -- see the module docstring for why load/store/
    mem_controller, despite bd_mem's real RAMB18E1, are deliberately left
    out."""
    table = table or Table()
    ops = set()
    for op, entries in table.by_op.items():
        for entry in entries:
            if set(entry.get("cells", ())) & STORAGE_CELLS:
                ops.add(op)
                break
    return ops


# ---------------------------------------------------------------------------
# The node graph: node index -> node index, via SSA values.
#
# Function arguments are deliberately NOT nodes here and cannot appear inside
# a cycle: they have no cell of their own (ArgSource, not a Node index) and
# are always an external boundary, which is exactly right -- a value flowing
# in from outside the function can never be part of a loop the function
# itself closes.

@dataclass(frozen=True)
class Edge:
    producer: int   # index into func.nodes
    consumer: int   # index into func.nodes
    value: str      # the SSA value name carrying this edge


def build_node_graph(func):
    """Returns (edges, adj): the full list of Edge, and node index -> set of
    successor node indices (deduplicated; a value graph can have parallel
    edges between the same two nodes -- e.g. two different results of X both
    feeding Y -- and SCC/Tarjan only cares about reachability, not multiplicity;
    the parallel edges themselves are kept in `edges` for reporting)."""
    edges: List[Edge] = []
    adj: Dict[int, Set[int]] = defaultdict(set)
    for i, node in enumerate(func.nodes):
        for result in node.results:
            for (consumer_idx, _operand_idx) in func.consumers.get(result, []):
                edges.append(Edge(i, consumer_idx, result))
                adj[i].add(consumer_idx)
    return edges, adj


# ---------------------------------------------------------------------------
# Tarjan's SCC, iterative (no recursion -- the real kernels' basic-block
# count makes recursion unlikely to blow the default limit, but an iterative
# form costs nothing extra and removes the question entirely).
#
# Restricted to a node subset: only edges whose BOTH endpoints are in
# `node_ids` are followed. This is what makes "delete the storage nodes and
# re-run Tarjan's" (Round 2 in the module docstring) a a well-defined
# operation on the same function, not a second copy of the graph.

def tarjan_scc(node_ids, adj):
    """Returns a list of SCCs (each a list of node indices), each SCC in
    discovery order. `adj` may contain edges leaving `node_ids` -- those are
    ignored, which is exactly what "graph restricted to node_ids" means."""
    node_set = set(node_ids)
    index_of: Dict[int, int] = {}
    lowlink: Dict[int, int] = {}
    on_stack: Dict[int, bool] = {}
    stack: List[int] = []
    counter = [0]
    sccs: List[List[int]] = []

    def neighbours(v):
        return (w for w in adj.get(v, ()) if w in node_set)

    for start in node_ids:
        if start in index_of:
            continue
        # work item: [node, neighbour_iterator]. Recursion is simulated with
        # this explicit stack; resuming a generator picks up exactly where
        # the last neighbour left off, which is what makes this equivalent
        # to the recursive textbook version.
        work = [[start, neighbours(start)]]
        index_of[start] = lowlink[start] = counter[0]
        counter[0] += 1
        stack.append(start)
        on_stack[start] = True

        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in index_of:
                    index_of[w] = lowlink[w] = counter[0]
                    counter[0] += 1
                    stack.append(w)
                    on_stack[w] = True
                    work.append([w, neighbours(w)])
                    advanced = True
                    break
                elif on_stack.get(w):
                    lowlink[v] = min(lowlink[v], index_of[w])
            if advanced:
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                lowlink[parent] = min(lowlink[parent], lowlink[v])
            if lowlink[v] == index_of[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on_stack[w] = False
                    comp.append(w)
                    if w == v:
                        break
                sccs.append(comp)
    return sccs


def _is_cycle(scc, adj):
    """A Tarjan component is a genuine cycle iff it has >1 node, or is a
    single node with a self-loop (its own result feeds one of its own
    operands). A lone node with no self-loop is always its own trivial SCC
    and is not a cycle -- Tarjan does not distinguish the two cases by
    itself, so this is checked separately."""
    if len(scc) > 1:
        return True
    (v,) = scc
    return v in adj.get(v, ())


# ---------------------------------------------------------------------------
# Check 1: cycles, and whether every one has storage.

def node_label(func, idx):
    node = func.nodes[idx]
    name = node.attrs.get("handshake.name")
    return f"{name} ({node.op})" if name else f"node{idx} ({node.op})"


@dataclass
class CycleViolation:
    """One storage-free cycle (a Round-2 SCC -- see module docstring): every
    node in it is confirmed to be a non-storage node, so this is a genuine
    combinational loop, not a heuristic guess."""
    nodes: List[int]
    node_labels: List[str]
    # Candidate bd_link insertion points: every edge with both endpoints
    # inside this cycle. A bd_link on ANY ONE of these breaks the cycle (it
    # removes that edge from the storage-free subgraph); this module reports
    # all of them and lets the emitter -- or a human -- pick, per the task
    # brief's "as a list of channels, not by mutating anything".
    channels: List[Tuple[str, str, str]]  # (producer_label, consumer_label, value)


@dataclass
class CycleReport:
    func_name: str
    n_nodes: int
    n_sccs: int              # non-trivial SCCs in the FULL graph (Round 1)
    n_storage_backed: int    # of those, how many contain >=1 storage node
    violations: List[CycleViolation]  # Round 2: genuinely storage-free cycles

    @property
    def ok(self):
        return not self.violations


def check_cycles(func, table=None):
    """Implements the two-round SCC check described in the module docstring.
    Never raises for a graph that actually has a comb loop -- that is a
    result to report (CycleReport.violations), not an exception; call
    assert_no_comb_loops() for the raise-on-failure form."""
    ops_with_storage = storage_ops(table)
    edges, adj = build_node_graph(func)
    all_ids = list(range(len(func.nodes)))

    # Round 1: diagnostic only.
    full_sccs = [c for c in tarjan_scc(all_ids, adj) if _is_cycle(c, adj)]
    storage_backed = sum(
        1 for c in full_sccs
        if any(func.nodes[v].op in ops_with_storage for v in c)
    )

    # Round 2: delete storage nodes from the node set entirely, re-run.
    residual_ids = [v for v in all_ids if func.nodes[v].op not in ops_with_storage]
    residual_sccs = [c for c in tarjan_scc(residual_ids, adj) if _is_cycle(c, adj)]

    violations = []
    for comp in residual_sccs:
        comp_set = set(comp)
        chans = [
            (node_label(func, e.producer), node_label(func, e.consumer), e.value)
            for e in edges
            if e.producer in comp_set and e.consumer in comp_set
        ]
        violations.append(CycleViolation(
            nodes=comp,
            node_labels=[node_label(func, v) for v in comp],
            channels=chans,
        ))

    return CycleReport(
        func_name=func.name,
        n_nodes=len(func.nodes),
        n_sccs=len(full_sccs),
        n_storage_backed=storage_backed,
        violations=violations,
    )


class CombinationalLoopError(Exception):
    """Raised by assert_no_comb_loops(). Carries the CycleReport so a caller
    can print the full detail rather than just a message."""

    def __init__(self, report: CycleReport):
        self.report = report
        lines = [f"{report.func_name}: {len(report.violations)} storage-free cycle(s)"]
        for v in report.violations:
            lines.append(f"  cycle: {' -> '.join(v.node_labels)} -> (back to start)")
        super().__init__("\n".join(lines))


def assert_no_comb_loops(func, table=None):
    report = check_cycles(func, table)
    if report.violations:
        raise CombinationalLoopError(report)
    return report


# ---------------------------------------------------------------------------
# Check 2: token conservation.

@dataclass
class TokenViolation:
    value: str
    producer_label: str
    n_consumers: int
    message: str


@dataclass
class TokenReport:
    func_name: str
    n_values: int
    violations: List[TokenViolation]

    @property
    def ok(self):
        return not self.violations


def _consumer_count(func, name):
    """Total consumers of `name`, merging the `#0` alias parse.py adds for a
    bare (ungrouped) value -- see parse.py's _resolve(): `%v` and `%v#0` can
    both appear as operand spellings for the SAME produced value, and a
    consumer count that only looked at one spelling would under-count."""
    n = len(func.consumers.get(name, []))
    if "#" not in name:
        n += len(func.consumers.get(f"{name}#0", []))
    return n


def check_tokens(func):
    """Every value a node or a function argument produces must have exactly
    one consumer -- the invariant --handshake-materialize is documented to
    establish (bdc/AUDIT.md section 5). This does not re-derive that pass;
    it verifies its output actually has the property on the file at hand."""
    violations: List[TokenViolation] = []
    n_values = 0

    def check_one(name, label):
        nonlocal n_values
        n_values += 1
        n = _consumer_count(func, name)
        if n == 0:
            violations.append(TokenViolation(
                value=name, producer_label=label, n_consumers=0,
                message=(
                    f"%{name} (produced by {label}) has NO consumer. Either "
                    f"--handshake-materialize did not run on this file (it "
                    f"should have inserted a sink), or this reader failed to "
                    f"see a real consumer -- a bug in parse.py's operand walk "
                    f"or in this check."
                ),
            ))
        elif n > 1:
            violations.append(TokenViolation(
                value=name, producer_label=label, n_consumers=n,
                message=(
                    f"%{name} (produced by {label}) has {n} consumers. Either "
                    f"--handshake-materialize did not run (it should have "
                    f"inserted a fork), or this reader double-counted one "
                    f"physical use as {n} operand references."
                ),
            ))

    for ch in func.args:
        if ch.ssa_name:
            check_one(ch.ssa_name, "function argument")
    for i, node in enumerate(func.nodes):
        label = node_label(func, i)
        for result in node.results:
            check_one(result, label)

    return TokenReport(func_name=func.name, n_values=n_values, violations=violations)


# ---------------------------------------------------------------------------
# Top-level per-function / per-module entry points.

def check_func(func, table=None):
    return check_cycles(func, table), check_tokens(func)


def check_module(funcs, table=None):
    """Skips declarations (no body -- is_declaration True): they have no
    nodes and nothing to check, the same way bdc/map.py only walks bodies."""
    return [
        (func, *check_func(func, table))
        for func in funcs
        if not func.is_declaration
    ]


# ---------------------------------------------------------------------------
# CLI, in the shape of bdc/map.py --report.

def report(paths):
    table = Table()
    worst = 0
    for path in paths:
        try:
            with open(path) as fh:
                funcs = parse.parse_module(fh.read(), filename=path)
        except Exception as e:  # noqa: BLE001 -- a parse failure is a result
            print(f"\n{path}\n  PARSE FAILED: {e}")
            worst = max(worst, 2)
            continue

        name = os.path.basename(os.path.dirname(os.path.dirname(path)))
        for func, cyc, tok in check_module(funcs, table):
            print(f"\n{name}  ({func.name}, {cyc.n_nodes} nodes)")
            print(f"    cycles (SCCs):      {cyc.n_sccs}")
            print(f"      with storage:     {cyc.n_storage_backed}")
            print(f"      storage-free:     {len(cyc.violations)}"
                  + ("  ** HARD ERROR **" if cyc.violations else ""))
            for v in cyc.violations:
                print(f"        cycle: {' -> '.join(v.node_labels)} -> (back to start)")
                print(f"          candidate bd_link insertion points:")
                for p, c, val in v.channels:
                    print(f"            {p}  --[%{val}]-->  {c}")
            print(f"    token conservation: {tok.n_values} values, "
                  f"{len(tok.violations)} violation(s)"
                  + ("  ** HARD ERROR **" if tok.violations else ""))
            for tv in tok.violations:
                print(f"        {tv.message}")
            if cyc.violations or tok.violations:
                worst = max(worst, 1)
    return worst


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--report", action="store_true",
                     help="print per-kernel cycle / token-conservation results")
    ap.add_argument("files", nargs="+")
    args = ap.parse_args()
    if not args.report:
        ap.error("nothing to do but --report yet")
    sys.exit(report(args.files))


if __name__ == "__main__":
    main()
