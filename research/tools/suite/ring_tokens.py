#!/usr/bin/env python3
"""ring_tokens.py MLIR -- does every cycle hold more storage than the tokens it carries need? (a DIAGNOSTIC, not a rule)

bdc's ring floor (bdc/emit.py RING_MIN_STAGES = 3, ring_depths) asks for three storage stages on every simple cycle,
which is right for a cycle that carries one token: "occupancy is half a token per stage, so one token already fills two
stages and needs a third to move into". A cycle that passes the loop header k times carries k tokens per iteration
(one per loop-carried value it threads: kernels/quadrec's a <- b <- c <- d <- f(a, b, c, d) ring threads four), and by
the same argument needs 2k + 1 stages.

Tokens on an edge: 1 for a back edge, i.e. a data input of a mux (operand >= 1), a merge or a control_merge whose
producer is in the same or a later basic block (handshake.bb); else 0. Stages on an edge: bdc's own choice, read from
its Emitter (linked channels and their ring_depths depth) plus the storage BDC_AUTO's rules add (merge out / result
links counted as ring_depths counts them, fork output links). The environment is read exactly as emit.py reads it, so
`BDC_AUTO=1 ring_tokens.py X` checks the AUTO design.

Edge weight = stages - 2 * tokens; a cycle is short when its weight is <= 0 (stages <= 2 * tokens). Floyd-Warshall,
then every node on a short cycle is listed. Exit 1 when one exists. It does not prove a design live: 2k + 1 is the
one-token rule generalised, checked here on one kernel (quadrec: deepening its four rotation back edges to 3 stages
made simcheck pass 10/10), and it says nothing about the deadlocks that rule M fixes (lfsrfind, nest3, nested).
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "bdc"))
import emit  # noqa: E402
import slack  # noqa: E402
from hs import parse  # noqa: E402


def bb(node):
    v = node.attrs.get("handshake.bb")
    return int(v.value) if v is not None else -1


def main():
    path = sys.argv[1]
    func = [f for f in parse.parse_module(open(path).read(), filename=path) if not f.is_declaration][0]
    e = emit.Emitter(func)
    stages = {v: e.depth.get(v, 1) for v in e.linked}
    for i, node in enumerate(func.nodes):
        nm = emit.instname(node, i)
        if len(node.results) == 2 and nm in emit.MERGE_OUT_LINK:
            for r in node.results:
                stages[r] = stages.get(r, 0) + 1
        if len(node.results) == 2 and nm in emit.MERGE_RES_LINK:
            stages[node.results[0]] = stages.get(node.results[0], 0) + emit.MERGE_RES_DEPTH
        if node.op == "fork":
            for r in node.results:
                if emit.vname(r) in emit.FORK_OUT_LINK:
                    stages[r] = stages.get(r, 0) + 1
    edges, _ = slack.build_node_graph(func)
    edges = [x for x in edges if x.value not in e.mem_absorbed]
    n = len(func.nodes)
    INF = float("inf")
    d = [[INF] * n for _ in range(n)]
    ntok = 0
    for x in edges:
        c, p = func.nodes[x.consumer], func.nodes[x.producer]
        k = c.operands.index(x.value) if x.value in c.operands else -1
        tok = int(((c.op == "mux" and k >= 1) or c.op in ("merge", "control_merge")) and 0 <= bb(c) <= bb(p))
        ntok += tok
        w = stages.get(x.value, 0) - 2 * tok
        if w < d[x.producer][x.consumer]:
            d[x.producer][x.consumer] = w
    for k in range(n):
        dk = d[k]
        for i in range(n):
            dik = d[i][k]
            if dik == INF:
                continue
            di = d[i]
            for j in range(n):
                if dik + dk[j] < di[j]:
                    di[j] = dik + dk[j]
    bad = [i for i in range(n) if d[i][i] <= 0]
    worst = min((d[i][i] for i in range(n)), default=INF)
    print(f"{func.name}: {len(e.linked)} linked channels, {ntok} back edges; worst cycle stages - 2 * tokens = {worst} "
          f"(short when <= 0)")
    if bad:
        print(f"{func.name}: {len(bad)} nodes on cycles with stages <= 2 * tokens: "
              + " ".join(emit.instname(func.nodes[i], i) for i in bad))
        return 1
    print(f"{func.name}: every cycle has more than 2 stages per token")
    return 0


if __name__ == "__main__":
    sys.exit(main())
