#!/usr/bin/env python3
"""protocol.py GRAPHDIR SIZES_VH -- PROGRAM.md FIRST item step 6: the protocol table for one base graph, from the
graph only (no RTL).  Rows:
  today            the measured period (the graph reproduces it exactly)
  storage          step 4's search restricted to storage (link depth, merge-output link)
  + fast fall      that, plus every delay chain of the design falling in one element (links, compute, merges, acks)
  deco             today's design with the decoupled one-token-a-stage controller (bd_deco_attempt) at the link stages
                   where the critical cycle changes polarity, greedily, while it helps (a stage whose replacement makes
                   a zero-token cycle is a deadlock in that design and is skipped)
  no falls         every falling arc at 0: an upper bound on what two-phase signalling could give
  floor            the worst cycle with no polarity change
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from whatif import G, polarity_floor  # noqa: E402
import search  # noqa: E402


def greedy(g, cands, chosen=(), min_gain=300):
    chosen = list(chosen); cur = search.predict(g, chosen)[0][0]
    while True:
        best = None
        for c in cands:
            if c in chosen: continue
            try:
                (lam, cyc), g2 = search.predict(g, chosen + [c])
            except ValueError:
                continue
            if best is None or lam < best[0]: best = (lam, c)
        if best is None or cur - best[0] < min_gain: return chosen, cur
        chosen.append(best[1]); cur = best[0]


def all_chains(g):
    insts = {n["inst"] for n in g.nodes if n.get("role") == "delay"}
    for i in insts: g.fastfall(i, strict=False)
    return g


def deco_greedy(g):
    """replace, one at a time, the link stage at a polarity change of the current critical cycle."""
    sc = g.stage_cells(); done = []; cur = g.copy(); lam, cyc = cur.period(); skipped = set()
    while True:
        flips = []
        for i in cyc:
            a = cur.arcs[i]; u, v = cur.nodes[a["u"]], cur.nodes[a["v"]]
            for x in (u, v):
                c = x.get("cell", "")
                if u["edge"] != v["edge"] and c in sc and c not in done and c not in skipped: flips.append(c)
        best = None
        for c in dict.fromkeys(flips):
            try:
                g2 = cur.copy().deco(c); l2, c2 = g2.period()
            except ValueError:
                skipped.add(c); continue
            if best is None or l2 < best[0]: best = (l2, c, g2, c2)
        if best is None or lam - best[0] < 300: return done, lam, skipped
        lam, c, cur, cyc = best; done.append(c)


def main():
    d, sizes = sys.argv[1], sys.argv[2]
    g = G(d)
    base = g.period()[0]
    cands = [c for c in search.candidates(g, sizes) if not c.startswith("fastfall")]
    st_ed, st_l = greedy(g, cands)
    g3 = g.copy()
    for e in st_ed: search.apply(g3, e)
    ff_l = all_chains(g3).period()[0]
    dd, d_l, sk = deco_greedy(g)
    nf = g.copy().nofall().period()[0]
    fl = polarity_floor(g)["R"][0]
    rows = [("today", base, ""), ("storage (step 4, no fast fall)", st_l, " ".join(st_ed)),
            ("storage + every chain falls fast", ff_l, ""),
            ("deco controller at the coupling stages", d_l, " ".join(c.split("udut.")[1] for c in dd) +
             ("; deadlock if also at " + ", ".join(c.split("udut.")[1] for c in sk) if sk else "")),
            ("every falling arc 0 (two-phase bound)", nf, ""), ("floor (no polarity change)", fl, "")]
    for name, v, note in rows:
        print("%-42s %8.2f ns  %5.2fx  %s" % (name, v / 1000, base / v, note))


if __name__ == "__main__":
    main()
