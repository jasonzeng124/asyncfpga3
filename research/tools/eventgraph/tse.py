#!/usr/bin/env python3
"""tse.py -- time separation of events on a timed marked graph (eventgraph.py's nodes.tsv / arcs.tsv).

The question rule H asks is a time separation: once a latch's controller has fallen (the latch closes, occurrence k),
how soon can an upstream controller launch the NEXT value towards it?  Rule H (cells/verify/tighten.py
earliest_disturbance) answers with a shortest walk in which every controller fires on its FIRST reached input (OR):
a lower bound, but one that ignores that a C element waits for ALL its inputs, and that the input it is still
missing is the next token's request.  Whether that request can already be waiting is a question about tokens.

On a marked graph (every event waits for all its in-arcs: T(v, k) >= T(u, k - o) + w for every arc u -> v with o
tokens), with arc weights that are lower bounds on the real delays, the unrolled graph gives, for the source event c
at occurrence 0 and any event v at occurrence m:
  AFTER      (c, 0) reaches (v, m): T(v, m) - T(c, 0) >= the LONGEST path (weights summed, every in-arc counted);
  BEFORE     (v, m) reaches (c, 0): v's m-th occurrence happens before c's; it is not a later token;
  UNORDERED  neither: no bound in either direction -- the separation may be anything, including negative.  This is
             the "token already waiting" case; it exists for (c, v) exactly when the tightest cycle through both holds
             >= 2 tokens.
The longest path is the separation lower bound used by time-separation analysis of marked graphs with min delays
(Burns; Hulgaard et al.); it is tight when every delay sits at its lower bound.

ARCS USED: kind 'and' only.  eventgraph.py marks an edge with no single enabling pin ('bind', 'eval_bind': OR
causality, or a cell it cannot evaluate -- CARRY4, FF) with ONE arc, the binding cause in that trace; another
input could cause it earlier at other delays, so those arcs are dropped here, never used as precedence.  Dropping
arcs only removes constraints: every AFTER bound stays a lower bound, and an event left without in-arcs becomes
UNORDERED (flagged), the conservative direction.

WHAT THE GRAPH IS: the steady state of one simulated run (periodic nets only; data nets are not nodes).  So the
bounds are for the loop's steady state at the delays of that trace's corner: not loop entry or exit, not paths whose
enabling depends on data the window did not exercise.
"""
import collections, csv

NEG = float("-inf")


def load(gdir, kinds=("and",)):
    nodes = list(csv.DictReader(open(gdir + "/nodes.tsv"), delimiter="\t"))
    arcs = []
    for a in csv.DictReader(open(gdir + "/arcs.tsv"), delimiter="\t"):
        if a["kind"] in kinds:
            arcs.append((int(a["u"]), int(a["v"]), int(a["w_ps"]), int(a["offset"])))
    return nodes, arcs


def _topo0(n, arcs):
    """Order of the nodes along offset-0 arcs (a DAG in a live graph)."""
    indeg = [0] * n; out = collections.defaultdict(list)
    for u, v, w, o in arcs:
        if o == 0:
            indeg[v] += 1; out[u].append(v)
    q = collections.deque(i for i in range(n) if indeg[i] == 0); order = []
    while q:
        x = q.popleft(); order.append(x)
        for y in out[x]:
            indeg[y] -= 1
            if indeg[y] == 0: q.append(y)
    if len(order) != n:
        raise ValueError("offset-0 arcs form a cycle")
    return order


def separations(n, arcs, c, M=8):
    """For source node c at occurrence 0: (after, before), each {(v, m): value}.
    after[(v, m)]  = longest path (c, 0) -> (v, m), m in 0..M (absent: not reached);
    before[(v, m)] = True if (v, m) reaches (c, 0), m in -M..0."""
    if any(o < 0 for _, _, _, o in arcs):
        raise ValueError("negative offsets: normalise the graph first")
    order = _topo0(n, arcs)
    pos = {x: i for i, x in enumerate(order)}
    into = collections.defaultdict(list); outof = collections.defaultdict(list)
    for u, v, w, o in arcs:
        into[v].append((u, w, o)); outof[u].append((v, w, o))
    T = {}
    for m in range(M + 1):
        for v in order:
            if v == c and m == 0:
                T[(v, 0)] = 0
                continue
            best = NEG
            for u, w, o in into[v]:
                t = T.get((u, m - o), NEG) if m - o >= 0 else NEG
                if t + w > best: best = t + w
            if best > NEG: T[(v, m)] = best
    B = {(c, 0): True}
    for m in range(0, -M - 1, -1):
        for v in reversed(order):
            if (v, m) in B: continue
            for y, w, o in outof[v]:
                if B.get((y, m + o)) and m + o <= 0:
                    B[(v, m)] = True; break
    return T, B


def classify(n, arcs, c, M=8):
    """Per node v: ('after', lb, m) for the earliest-bounded occurrence not before c, or ('unordered', m) for the first
    occurrence that is neither, or ('open', None) when the window -M..M does not settle it (raise M)."""
    T, B = separations(n, arcs, c, M)
    out = {}
    for v in range(n):
        res = None; lbs = []
        for m in range(-M, M + 1):
            if B.get((v, m)):
                continue
            if (v, m) in T:
                lbs.append((T[(v, m)], m))
            else:
                if m < 0 and not any(B.get((v, k)) for k in range(-M, m)):
                    res = ("open", None); break    # nothing before it either: the window is too short
                res = ("unordered", m); break
        if res is None:
            res = ("after",) + min(lbs) if lbs else ("open", None)
        out[v] = res
    return out


if __name__ == "__main__":
    import sys
    g = sys.argv[1]
    nodes, arcs = load(g)
    n = len(nodes)
    for i, nd in enumerate(nodes):
        if nd["cell"].endswith("ctl.u.u") and nd["edge"] == "F":
            cl = classify(n, arcs, i)
            cnt = collections.Counter(r[0] for r in cl.values())
            print(nd["cell"], nd["phase_ps"], dict(cnt))
