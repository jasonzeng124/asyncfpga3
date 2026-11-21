#!/usr/bin/env python3
"""margin/carryring/summarize.py OUT/ ROUTE (shard C, UNTRUSTED): per-kind summary of loops.py's rings_rctree.tsv
(build_net RC_TREE=1, research's RC tree) and rings_default.tsv (build_net default arcs) against research's
predicted.tsv; the >3 % disagreements with their per-stage cause (seg_*.tsv); dP/dy per kind and the y resolution a
board measurement gives at 1 % per-ring scatter (ring128's median scatter 0.76 %)."""
import csv, os, re, statistics as st, sys
from collections import defaultdict

O, ROUTE = sys.argv[1], sys.argv[2]
ORDER = ["L8", "L16", "C1", "C4", "C16", "C32", "F8", "F16"]
out = []
p = out.append


def rows(f):
    return list(csv.DictReader(open(os.path.join(O, f)), delimiter="\t"))


def segs(f):
    by = defaultdict(list)
    for r in rows(f):
        by[r["ring"]].append(r)
    return by


def stage(c):
    return re.sub(r"\[\d+\]", "[]", c).split(".", 2)[-1]


for model in ("rctree", "default"):
    R = rows("rings_%s.tsv" % model)
    S = segs("seg_%s.tsv" % model)
    bad = [r for r in R if r["cyc"] != "1" or r["same_cells"] != "yes"]
    p("## route %s, formal model %s (build_net %s)" % (ROUTE, model, "RC_TREE=1" if model == "rctree" else "default"))
    p("loops: %d rings, %d with exactly one decoded cycle through the same cells (in order) as research's walk%s"
      % (len(R), len(R) - len(bad), "" if not bad else "; NOT: " + " ".join(r["ring"] for r in bad)))
    by = defaultdict(list)
    for r in R:
        if r["cyc"] == "1":
            by[r["kind"] + r["n"]].append(r)
    p("kind  n | formal P(.288,.2) P(.288,1) ns (median) | formal/research ratio mean [min, max]: P(.288,.2)  P(.288,1)  "
      "FAST_MIN  SLOW_MAX | dP/dy ps: formal research | %/unit y | sigma_y per ring, per kind (8 rings) at 1 % scatter")
    for k in ORDER:
        v = by.get(k, [])
        if not v:
            continue
        f = lambda c: [float(r[c]) for r in v]
        rr = lambda c: "%.4f [%.4f, %.4f]" % (st.mean(f(c)), min(f(c)), max(f(c)))
        dy = st.median(f("f_dPdy")); rdy = st.median(f("r_dPdy")); p02 = st.median(f("f_P02"))
        sig = (0.01 * p02 / dy) if dy else float("inf")
        p("%-4s %2d | %6.2f %6.2f | %s  %s  %s  %s | %5.0f %5.0f | %5.1f%% | %s" % (
            k, len(v), p02 / 1000, st.median(f("f_P10")) / 1000, rr("q_P02"), rr("q_P10"), rr("q_Pmin"), rr("q_Pmax"),
            dy, rdy, 100 * dy / p02, "inf (no y arcs)" if not dy else "%.3f, %.3f" % (sig, sig / len(v) ** .5)))
    dis = [(r, t) for r in R if r["cyc"] == "1" for t in ("P02", "P10", "Pmin", "Pmax") if abs(float(r["q_" + t]) - 1) > 0.03]
    rings = sorted({r["ring"] for r, _ in dis})
    p("rings differing from research by > 3 %% at any of the four points: %d of %d" % (len(rings), len(R)))
    if dis:
        # cause, per stage type: formal (wire into the cell + cell arc) - research (INTERCONNECT + IOPATH), FAST_MIN / SLOW_MAX
        agg = defaultdict(list)
        for ring in rings:
            for s in S[ring]:
                agg[stage(s["cell"])].append((int(s["F_wire_lo"]) + int(s["F_cell_lo"]) - int(s["R_wire_lo"]) - int(s["R_cell_lo"]),
                                              int(s["F_wire_hi"]) + int(s["F_cell_hi"]) - int(s["R_wire_hi"]) - int(s["R_cell_hi"]),
                                              int(s["F_cell_lo"]) - int(s["R_cell_lo"])))
        p("  per stage (formal - research, ps per stage, median [min, max]; 'cell' = the stage's cell arc alone, formal's includes the input site pin):")
        for c, v in sorted(agg.items()):
            md = lambda i: "%+.0f [%+d, %+d]" % (st.median(x[i] for x in v), min(x[i] for x in v), max(x[i] for x in v))
            p("    %-16s %4d stages  FAST_MIN %s  SLOW_MAX %s  (cell arc %s)" % (c, len(v), md(0), md(1), md(2)))
    if model == "default":
        # the band position at which formal's default arcs give research's L-ring periods (A17's coordinate shift)
        xs = [(float(r["r_P02"]) - float(r["f_lo"])) / float(r["f_R"]) for r in R if r["kind"] == "L"]
        xe = st.median(xs)
        p("default arcs: x at which formal's L rings reproduce research's L rings at x 0.288: median %.3f [%.3f, %.3f];"
          " at that x, formal/research per kind (y 0.2 / y 1.0):" % (xe, min(xs), max(xs)))
        for k in ORDER:
            v = by.get(k, [])
            q2 = [(float(r["f_lo"]) + xe * float(r["f_R"]) + .2 * float(r["f_CF"])) / float(r["r_P02"]) for r in v]
            q10 = [(float(r["f_lo"]) + xe * float(r["f_R"]) + 1. * float(r["f_CF"])) / float(r["r_P10"]) for r in v]
            p("    %-4s %.3f [%.3f, %.3f] / %.3f [%.3f, %.3f]" % (k, st.mean(q2), min(q2), max(q2), st.mean(q10), min(q10), max(q10)))
    p("")
open(os.path.join(O, "summary.txt"), "w").write("\n".join(out) + "\n")
print("\n".join(out))
