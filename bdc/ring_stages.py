#!/usr/bin/env python3
"""Count storage stages on a loop's ring, for one handshake-dialect MLIR file.

WHY.  On silicon each kernel costs a similar amount per loop iteration almost
independently of what the loop computes, which is the signature of a cost paid
per handshake round trip rather than per operation.  Dividing by the storage
stages the token traverses per iteration is the natural way to normalise it.

BUT DO NOT OVERSELL THE DIVISION.  Re-measured 2026-08-24, with op fusion on by
default (it was off until 2026-08-23, and every number in the previous version
of this docstring came from the 2.5x looser circuit that produced):

    kernel      stages   ns/iter   ns/stage
    xorshift       6       49.6      8.27
    ipow           6       60.0     10.00
    collatz        7       93.2     13.31
    collatz64      7      118.6     16.94

Fusion shortened the rings as well as the datapath -- these were 7/9/9 stages
before -- so both terms moved.  And ns/stage spans 2.0x across four kernels
while ns/iter spans 2.4x, so normalising by stage count explains almost none of
the spread.  Two of these rows settle why: collatz and collatz64 have the SAME
ring at 7 stages and differ by 27%, which is datapath width alone, and xorshift
and ipow have the same ring at 6 stages and differ by 21%, which is three
shifts and three xors against two 32-bit multiplies.  Stage count is a real
term, not the only one, and per-stage cost is not a constant of the fabric.

Measurements and their error bars: cells/hw/README.md, "What a loop iteration
costs, across every kernel measured".

A stage on a LOOP is not a pipeline stage.  A loop with a carried dependency
holds one token, so the token goes all the way round before the next
iteration starts and every stage on the ring is serial latency paid every
iteration.  RING_MIN_STAGES=3 is the correctness floor; anything above it is
a policy choice, and emit.py's rule 1 (measurability_sites) is the reason we
are at 6-7 (7-9 before op fusion).

WHAT IT REPORTS.  For each strongly connected component that is a real cycle:
the heaviest simple cycle in it, weighted by storage stages.  The heaviest,
not the lightest, because the iteration cannot finish until the slowest
recurrence closes -- ring_depths() in emit.py wants the LIGHTEST cycle for
the opposite reason (the floor has to hold everywhere).

Two honest limits.  The heaviest simple cycle is an upper bound on what one
iteration traverses, not a proof: the cycle that actually carries the loop
variable may be shorter.  And a kernel with NESTED loops (gcd) mixes rings,
so its measured ns/iteration cannot be divided by any single stage count --
xorshift, collatz and collatz64 are single loops and are the clean rows.

Usage:
    python3 bdc/ring_stages.py build/frontend/xorshift/comp/handshake_transformed.mlir
    python3 bdc/ring_stages.py --source bdc build/frontend/*/comp/*.mlir

--source picks where the stage counts come from:
    bdc        this backend's own placement, via emit.Emitter (default)
    buffer     handshake.buffer ops already in the file, e.g. after
               Dynamatic's --handshake-place-buffers.  Use this to compare
               against Dynamatic on the same graph.
"""
import argparse, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import slack                      # noqa: E402
from hs import parse              # noqa: E402
from map import Table             # noqa: E402

sys.setrecursionlimit(200000)


def heaviest_ring(sub, w, cap=3_000_000):
    """(stages, nodes) of the heaviest simple cycle, and how many were walked.

    Plain DFS with the standard `v > start` pruning so each cycle is found
    once.  `cap` bounds the walk: these graphs are a few hundred nodes and
    the count is reported so a truncated answer can never be mistaken for a
    complete one."""
    best = (0, 0)
    walked = [0]
    for start in sorted(sub):
        path = [start]
        onpath = {start}

        def dfs(u, acc):
            nonlocal best
            if walked[0] > cap:
                return
            for v in sorted(sub.get(u, ())):
                if v == start:
                    walked[0] += 1
                    tot = acc + w.get((u, v), 0)
                    if tot > best[0]:
                        best = (tot, len(path))
                elif v not in onpath and v > start:
                    onpath.add(v)
                    path.append(v)
                    dfs(v, acc + w.get((u, v), 0))
                    path.pop()
                    onpath.discard(v)
                if walked[0] > cap:
                    return
        dfs(start, 0)
    return best, walked[0]


def stage_weights(func, source, table):
    """{(producer, consumer): stages} for one function."""
    edges, _ = slack.build_node_graph(func)
    if source == "bdc":
        import emit
        em = emit.Emitter(func, table)
        per_value = {v: em.depth.get(v, 1) for v in em.linked}
    else:
        # A handshake.buffer node IS the storage; its slot count is the depth.
        per_value = {}
        for i, node in enumerate(func.nodes):
            if node.op != "buffer":
                continue
            slots = 1
            for key in ("num_slots", "numSlots", "slots"):
                got = getattr(node, "attrs", {}).get(key) if hasattr(node, "attrs") else None
                if got is not None:
                    try:
                        slots = int(str(got).split(":")[0].strip())
                    except ValueError:
                        pass
                    break
            for r in node.results:
                per_value[r] = slots
    w = {}
    for e in edges:
        key = (e.producer, e.consumer)
        w[key] = max(w.get(key, 0), per_value.get(e.value, 0))
    return edges, w


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--source", choices=("bdc", "buffer"), default="bdc")
    ap.add_argument("files", nargs="+")
    args = ap.parse_args()

    table = Table()
    for path in args.files:
        name = os.path.basename(os.path.dirname(os.path.dirname(path))) or path
        for func in parse.parse_module(open(path).read(), filename=path):
            edges, w = stage_weights(func, args.source, table)
            _, adj = slack.build_node_graph(func)
            ids = list(range(len(func.nodes)))
            cyc = [s for s in slack.tarjan_scc(ids, adj) if slack._is_cycle(s, adj)]
            if not cyc:
                print(f"{name:12s} {func.name:14s} no cycles")
                continue
            for scc in sorted(cyc, key=len, reverse=True):
                members = set(scc)
                sub = {u: {v for v in adj[u] if v in members} for u in scc}
                (stages, nodes), walked = heaviest_ring(sub, w)
                trunc = "  (TRUNCATED -- walk hit the cap)" if walked > 3_000_000 else ""
                print(f"{name:12s} {func.name:14s} SCC {len(scc):3d} nodes"
                      f"  heaviest ring = {stages:3d} stages over {nodes:3d} nodes"
                      f"  [{walked} cycles walked]{trunc}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
