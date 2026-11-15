#!/usr/bin/env python3
"""tsehold.py GRAPH_DIR CORNER_SDF [--guard-frac F] [--guard-min PS] [--only RX] -- rule H with C-element semantics and
token counts: the hold check of every Muller link / pipe stage, with the upstream controllers' firing times taken from
a time-separation bound on the route's marked graph instead of rule H's OR walk.

GRAPH_DIR: eventgraph.py's output (nodes.tsv, arcs.tsv) for a run at the SAME delay corner as CORNER_SDF -- for hold,
a DUMP_FIELD=min fullstack_dump.sh run and a corner_sdf.py --band 0 SDF of the same route (soak_routed.json beside it,
as corner_audit.py lays it out).

Per latch controller L (a Muller C node with latch enables; tighten.py's rule H loop):
  t_en   the latch closes: enable arrival + the LUT arc, from L's fall (as rule H);
  OR     rule H's own number: earliest_disturbance, every state node firing on its first reached input;
  TSE    every state node that is an event of the graph fires no earlier than tse.classify's bound for its first
         occurrence that is not before L's close (longest path in the unrolled marked graph, 'and' arcs only); state
         nodes not in the graph (data latch bits, cells whose edges were aperiodic) fire on their first reached input,
         as in rule H, from the start's fall and from the graph nodes' bounds.  An UNORDERED graph node (some
         occurrence neither before nor after L's close: a token may already be waiting) that reaches L's data pins is
         listed and counts as a violation: the graph gives no bound for it.
  margin = earliest data arrival - t_en - guard, guard = max(frac * t_en, min) (rule H's req_guard).
Muller stages only; a bd_link_dc capture node and a controller with no event in the graph (aperiodic in this run: an
exit path, a steer side not taken) are reported as NOT COVERED with their OR number.
"""
import sys, os, re, heapq, math, collections, argparse, csv

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "../../.."))
ap = argparse.ArgumentParser()
ap.add_argument("graph"); ap.add_argument("sdf")
ap.add_argument("--guard-frac", type=float, default=0.03); ap.add_argument("--guard-min", type=int, default=50)
ap.add_argument("--lo", type=float, default=0.97); ap.add_argument("--hi", type=float, default=1.03)
ap.add_argument("--min-only", action="store_true", help="the min-delay bound only (no interval / reference events)")
ap.add_argument("--only", default=None); ap.add_argument("-M", type=int, default=8)
a = ap.parse_args()
sys.argv = [sys.argv[0], a.sdf]
sys.path.insert(0, os.path.join(ROOT, "cells/verify")); sys.path.insert(0, HERE)
import tighten as T  # noqa: E402
import tse  # noqa: E402
import maxplus  # noqa: E402


def guard(t):
    return max(int(a.guard_frac * t), a.guard_min)


import pathlib
edges, back, stops = T.routed_graph(pathlib.Path(a.sdf))
timing = T.Timing(edges, stops)
nodes, _, unbounded = tse.load(a.graph, with_unbounded=True)
n = len(nodes)
_all = [dict(u=int(x["u"]), v=int(x["v"]), w=int(x["w_ps"]), o=int(x["offset"]), k=x["kind"])
        for x in csv.DictReader(open(a.graph + "/arcs.tsv"), delimiter="\t")]
# one relabelling for every kind (maxplus.normalize's Bellman-Ford, kept here for its potentials): event (x, m) of the
# normalised graph is iteration m + pot[x] of the trace, at phase_x + (m + pot[x]) * P
pot = [0] * n
for _ in range(n + 1):
    ch = False
    for e in _all:
        if pot[e["u"]] + e["o"] < pot[e["v"]]:
            pot[e["v"]] = pot[e["u"]] + e["o"]; ch = True
    if not ch: break
else:
    raise SystemExit("a cycle with a negative token count")
_all = [dict(e, o=e["o"] + pot[e["u"]] - pot[e["v"]]) for e in _all]
PERIOD = int(re.search(r"period P = (\d+)", open(a.graph + "/check.txt").read()).group(1))
trace_t = lambda x, m: int(nodes[x]["phase_ps"]) + (m + pot[x]) * PERIOD
selfcheck = [0, 0, None]      # bounds checked, bounds above the trace's own separation, worst excess
arcs = [(e["u"], e["v"], e["w"], e["o"]) for e in _all if e["k"] == "and"]
uarcs = [(e["u"], e["v"], e["w"], e["o"]) for e in _all if e["k"] in ("and", "bind")]
LO, HI = a.lo, a.hi
by_cell = collections.defaultdict(list)
for i, nd in enumerate(nodes):
    by_cell[nd["cell"]].append(i)
inst_of = lambda p: T.pin_split(p)[0]
graph_stops = {s for s in stops if inst_of(s) in by_cell}
print(f"graph {a.graph}: {n} events, {len(arcs)} 'and' arcs; SDF {a.sdf}: {len(stops)} state nodes, "
      f"{len(graph_stops)} of them events of the graph")
controllers = sorted(s for s in stops if T.latch_enables(edges, s))
latch_owner, en_at = {}, {}      # latch instance -> its controller; (ctl, latch inst) -> enable arrival + LUT arc
for ctl in controllers:
    for p, d in T.latch_enables(edges, ctl):
        li = inst_of(p)
        latch_owner[li] = ctl
        arc = max((x for _, x in edges.get(p, ())), default=0)
        en_at[(ctl, li)] = min(en_at.get((ctl, li), math.inf), d + arc)


def node_bound(cl, inst, edge=None):
    """('after', lb) over every graph event of `inst` (of one edge, if given), or ('unordered', why) / ('absent',)."""
    ids = [i for i in by_cell.get(inst, ()) if edge is None or nodes[i]["edge"] == edge]
    if not ids:
        return ("absent",)
    rs = [cl[i] for i in ids]
    bad = [r for r in rs if r[0] != "after"]
    return ("unordered", bad[0]) if bad else ("after", min(r[1] for r in rs))


rows = []
for ctl in controllers:
    label = inst_of(ctl)
    if a.only and not re.search(a.only, label):
        continue
    enables = T.latch_enables(edges, ctl)
    en_pins = {p for p, _ in enables}
    insts = {inst_of(p) for p in en_pins}
    t_en = max(d + max((x for _, x in edges.get(p, ())), default=0) for p, d in enables)
    d_pins = T.latch_data_pins(back, insts, en_pins)
    if not d_pins:
        continue
    own = lambda pin, insts=insts: inst_of(pin) in insts
    dc = T.dc_link_of(ctl)
    t_or, reached = T.earliest_disturbance(timing, ctl, d_pins, own, falls=dc is None)
    m_or = (t_or - t_en - guard(t_en)) if t_or is not None else None
    closes = [i for i in by_cell.get(label, ()) if nodes[i]["edge"] == "F"]
    if dc is not None or not closes:
        rows.append((label, t_en, m_or, None, "NOT COVERED: " + ("bd_link_dc" if dc else "no event in the graph"), []))
        continue
    # launch points: storage whose output reaches a data pin with no storage in between
    launch = {}
    for s in stops:
        if own(s) or s == ctl:
            continue
        hits = [d for p, d in timing.early_any(s).items() if p in d_pins]
        if hits:
            launch[s] = min(hits)
    worst = None
    for c in closes:
        T_, B_ = tse.separations(n, arcs, c, a.M)
        def first_not_before(i):
            for m_ in range(-a.M, a.M + 1):
                if not B_.get((i, m_)):
                    return m_
            return None
        plan = {}                                  # launch pin -> (graph node ids or None, extra delay, kind)
        for s_, comb in launch.items():
            li = inst_of(s_)
            if li in latch_owner:
                x = latch_owner[li]
                ids = [i for i in by_cell.get(inst_of(x), ()) if nodes[i]["edge"] == "R"]
                plan[s_] = (ids, en_at[(x, li)] + comb, "latch", inst_of(x))
            else:
                plan[s_] = (list(by_cell.get(li, ())), comb, "node", li)
        targets = sorted({(i, first_not_before(i)) for ids, _, _, _ in plan.values() for i in ids
                          if first_not_before(i) is not None})
        res = {}
        if targets and not a.min_only:
            for win in (a.M // 2, a.M, 2 * a.M):     # the unfolding must reach back to where every source is before r
                try:
                    res = tse.interval_sep(n, arcs, c, targets, win, LO, HI, uarcs=uarcs, unbounded=unbounded)
                    break
                except ValueError as ex:
                    if "window too short" not in str(ex) or win == 2 * a.M:
                        raise
        def tbound(t):
            b = res.get(t, (None, None))[0]
            if t in T_:
                b = max(b, LO * T_[t]) if b is not None else LO * T_[t]
            if b is not None:                      # the trace is one execution inside the interval: never above it
                sep = trace_t(*t) - trace_t(c, 0)
                selfcheck[0] += 1
                if b > sep + 1:
                    selfcheck[1] += 1
                    selfcheck[2] = max(selfcheck[2] or 0, b - sep)
            return b                               # None: unordered and no reference event bounds it
        best, bad, kinds = (math.inf, None), [], collections.Counter()
        for s_, (ids, extra, kind, who) in plan.items():
            if not ids:
                t, k = reached.get(s_, 0) + LO * extra, kind + "/aperiodic(OR)"
            else:
                bs = [tbound((i, first_not_before(i))) if first_not_before(i) is not None else None for i in ids]
                if any(b is None for b in bs):
                    bad.append((who, ("unordered", None), int(extra))); kinds[kind + "/unbounded"] += 1; continue
                t, k = min(bs) + LO * extra, kind + "/graph"
            kinds[k] += 1
            if t < best[0]:
                best = (t, (inst_of(s_), k))
        te = HI * t_en
        m = (best[0] - te - guard(te)) if best[0] < math.inf else None
        key = (-1 if bad else 0, m if m is not None else math.inf)
        if worst is None or key < worst[0]:
            worst = (key, nodes[c]["phase_ps"], m, best[1], bad, kinds)
    _, ph, m, via, bad, kinds = worst
    note = f"close@{ph} via {via[0].replace('bridge_i.udut.', '')} [{via[1]}]" if via else f"close@{ph}"
    rows.append((label, t_en, m_or, m, note + " " + ",".join(f"{k}:{v}" for k, v in sorted(kinds.items())), bad))

print(f"{'controller':<50} {'t_en':>5} {'OR':>7} {'TSE':>7}  note")
for label, t_en, m_or, m, note, bad in sorted(rows, key=lambda r: (0 if r[5] else 1, r[3] if r[3] is not None else 1e9)):
    f = lambda x: "-" if x is None else str(int(x))
    print(f"{label.replace('bridge_i.udut.', ''):<50} {t_en:>5} {f(m_or):>7} {f(m):>7}  {note}"
          + ("  UNORDERED: " + "; ".join(f"{s.replace('bridge_i.udut.', '')} m={w[1]} path {tt}"
                                         for s, w, tt in sorted(set(bad), key=lambda b: b[2])[:4])
             if bad else ""))
cov = [r for r in rows if not r[4].startswith("NOT")]
print(f"covered {len(cov)}: TSE below 0 {sum(1 for r in cov if r[3] is not None and r[3] < 0)}, unordered "
      f"{sum(1 for r in cov if r[5])}; OR below 0 (covered) {sum(1 for r in cov if r[2] is not None and r[2] < 0)}; "
      f"not covered {len(rows) - len(cov)} (OR below 0 there: "
      f"{sum(1 for r in rows if r[4].startswith('NOT') and r[2] is not None and r[2] < 0)})")
print(f"self-check: {selfcheck[0]} bounds against the trace's own separations, {selfcheck[1]} above it"
      + (f" (worst by {selfcheck[2]:.0f} ps) -- BOUNDS INVALID" if selfcheck[1] else " -- consistent"))
