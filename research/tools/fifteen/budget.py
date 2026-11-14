#!/usr/bin/env python3
"""budget.py GRAPHDIR DELAYS_TSV [--guard 0.772] -- PROGRAM.md FIRST (xorshift at 15 ns), step 1: the budget of one
route's critical cycle, from its timed event graph (research/tools/eventgraph) and itercost's per-delay settle table
(research/tools/itercost/analyze.py delays.tsv, same run).

1. Falling arcs on the critical cycle, by kernel instance and cell role, and where the cycle changes polarity.
2. Each delay on the rising ring: its time on the cycle, the worst settle of the data it bundles over the whole run
   (entry and exit included), the delay the rules need for that settle (settle / GUARD_LO, cells/verify/skew.py) and
   the removable part.  The select rule (never shorten a mux delay or a select link) is reported, not applied.
3. Each rising req/ack wire between handshake cells: routed delay against an adjacent-cell wire (the 10th percentile
   of all wires in the graph).
4. The graph's period with all three taken: only rising arcs (falling arcs off the cycle, i.e. the worst cycle with no
   polarity change), every delay scaled down to its need (the select rule waived), every handshake wire at the
   adjacent value.  And each of the three alone.
"""
import sys, os, re, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../eventgraph"))
import maxplus  # noqa: E402
from whatif import G  # noqa: E402

GUARD_LO = float(sys.argv[sys.argv.index("--guard") + 1]) if "--guard" in sys.argv else 0.772
SELECT = re.compile(r"^(umux\d+|ulink_n12__\d|ucontrol_merge0_olink|ulink_n_index)")


def load(d, dt):
    g = G(d)
    rows = [l.rstrip("\n").split("\t") for l in open(d + "/arcs.tsv")]
    h = rows[0]
    for a, r in zip(g.arcs, rows[1:]):
        x = dict(zip(h, r)); a["wire"] = int(x["wire_ps"]); a["arcd"] = int(x["arc_ps"])
    dl = [dict(zip(*[l.rstrip("\n").split("\t") for l in (open(dt).readline(),)], )) for _ in ()]
    rows = [l.rstrip("\n").split("\t") for l in open(dt)]
    dl = [dict(zip(rows[0], r)) for r in rows[1:]]
    return g, dl


def scaled(g, dl, delays=True, wires=True, rise_only=True, wadj=None):
    arcs = []
    f = {}
    for d in dl:
        on = float(d["time_on_cycle_ps"]); ws = d["worst_settle_over_run_ps"]
        need = max(float(ws), 0) / GUARD_LO if ws not in ("-", "") else 0
        f[(d["instance"], d["kind"])] = min(1.0, need / on) if on > 0 else 1.0
    for a in g.arcs:
        u, v = g.nodes[a["u"]], g.nodes[a["v"]]
        if rise_only and (u["edge"] != "R" or v["edge"] != "R"): continue
        b = dict(a)
        if delays and v.get("role") == "delay":
            m = re.search(r"udut\.(.+?)\.(udly|rdly|uack|us)\.chain", v.get("cell", "")) or \
                re.search(r"udut\.(.+?)\.uor$", v.get("cell", ""))
            if m:
                key = (m.group(1).replace(".many.stage[1].u", "").replace(".many.stage[0].u", ""),
                       m.group(2) if m.lastindex and m.lastindex >= 2 else "udly")
                b["w"] = a["w"] * f.get(key, f.get((m.group(1), "udly"), 1.0))
        if wires and v.get("role") == "handshake" and v["edge"] == "R" and a["wire"] > wadj:
            b["w"] = a["w"] - (a["wire"] - wadj)
        arcs.append(b)
    return arcs


def main():
    d, dt = sys.argv[1], sys.argv[2]
    g, dl = load(d, dt)
    lam, cyc = g.period()
    wires = sorted(a["wire"] for a in g.arcs)
    wadj = wires[len(wires) // 10]
    print("route %s: period %.2f ns, critical cycle %d arcs; adjacent-cell wire (p10 of %d) %d ps" % (
        d, lam / 1e3, len(cyc), len(wires), wadj))
    # 1. falling arcs
    fall = collections.Counter(); flips = []
    for i in cyc:
        a = g.arcs[i]; u, v = g.nodes[a["u"]], g.nodes[a["v"]]
        if v["edge"] == "F": fall[(v["inst"], v.get("role"))] += a["w"]
        if u["edge"] != v["edge"]: flips.append("%s%s->%s%s" % (u["inst"], u["edge"], v["inst"], v["edge"]))
    print("1. falling arcs on the cycle: %.2f ns" % (sum(fall.values()) / 1e3))
    for (inst, r), w in fall.most_common(): print("   %-28s %-9s %6d ps" % (inst, r, w))
    print("   polarity changes: %s" % ", ".join(flips))
    # 2. delays
    print("2. delays on the rising ring (need = worst settle over the run / %.3f):" % GUARD_LO)
    rem = rem_sel = 0
    for x in dl:
        on = float(x["time_on_cycle_ps"]); ws = x["worst_settle_over_run_ps"]
        need = max(float(ws), 0) / GUARD_LO if ws not in ("-", "") else 0
        r = max(0, on - need); sel = bool(SELECT.match(x["instance"]))
        rem += r; rem_sel += r if sel else 0
        print("   %-24s %-5s on cycle %5.0f  per-iteration logic %5s  worst settle %6s  need %5.0f  removable %5.0f%s" % (
            x["instance"], x["kind"], on, x["logic_ps"], ws, need, r, "  (select rule: kept)" if sel else ""))
    print("   removable %.2f ns, of which %.2f ns on select paths (the select rule keeps them)" % (rem / 1e3, rem_sel / 1e3))
    # 3. wires
    hw = [(g.nodes[g.arcs[i]["v"]]["inst"], g.arcs[i]["wire"]) for i in cyc
          if g.nodes[g.arcs[i]["v"]].get("role") == "handshake" and g.nodes[g.arcs[i]["v"]]["edge"] == "R"]
    print("3. rising handshake wires on the cycle: %.2f ns, adjacent %.2f ns -> removable %.2f ns" % (
        sum(w for _, w in hw) / 1e3, len(hw) * wadj / 1e3, sum(max(0, w - wadj) for _, w in hw) / 1e3))
    # 4. predicted
    def mcr(arcs):
        l, c = maxplus.mcr(len(g.nodes), arcs); return l
    out = [("RTZ off the cycle only (worst cycle with no polarity change)", scaled(g, dl, False, False, True, wadj)),
           ("delays at need only (falls kept)", scaled(g, dl, True, False, False, wadj)),
           ("wires adjacent only (falls kept)", scaled(g, dl, False, True, False, wadj)),
           ("all three", scaled(g, dl, True, True, True, wadj))]
    print("4. predicted period:")
    for name, arcs in out:
        print("   %-62s %6.2f ns" % (name, mcr(arcs) / 1e3))


if __name__ == "__main__":
    main()
