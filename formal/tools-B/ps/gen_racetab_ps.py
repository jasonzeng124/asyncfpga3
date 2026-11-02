#!/usr/bin/env python3
"""Shard B: generate Formal/Cells/RaceTablePS.lean from racetab.py outputs (rt*.json): per storage node, the row with
the smallest corner-uniform threshold among its necessary self-induced episodes. usage: gen_racetab_ps.py NET.json OUT.lean RT.json..."""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__))
N = json.load(open(sys.argv[1])); g = N["gates"]; OUT = sys.argv[2]
best = {}; nrows = 0; nonnec = set()
for f in sys.argv[3:]:
    for r in json.load(open(f)):
        nrows += 1
        if not r["necessary"]: nonnec.add(r["node"]); continue
        k = r["kappa_all_corners"] if r["kappa_all_corners"] is not None else -1
        if r["node"] not in best or k < best[r["node"]][0]: best[r["node"]] = (k, r)
rows = sorted(best.values(), key=lambda x: x[0])
fmt = lambda l: "[" + ", ".join("⟨%d, %d, %d, %d⟩" % tuple(g[m]["arcs"][p][k] for k in ("fmin", "fmax", "smin", "smax")) for m, p in l) + "]"
out = [open(os.path.join(HERE, "racetab_head.lean")).read()]
out.append("-- %d rows (one per storage node; %d episode records from %d files; smallest threshold first)." % (len(rows), nrows, len(sys.argv) - 3))
out.append("set_option maxHeartbeats 0 in\nset_option maxRecDepth 100000 in\ndef raceTable : List Row := [\n  " + ",\n  ".join("⟨%d, %s, %s⟩" % (r["gate"], fmt(r["path"]), fmt(r["loop"])) for _, r in rows) + "]\n")
out.append("""theorem table_ok : raceTable.all rowOK = true := by decide +kernel

theorem table_len : raceTable.length = %d := by decide +kernel

/-- **Every recorded acknowledgement race of THE target is safe at κ = 0.415, at every corner**: for every row, every
corner c ∈ [0,1] and every admissible delays, the feedback loop's total delay is at most the path's. -/
theorem table_race_free : ∀ r ∈ raceTable, ∀ {p : DelayPar}, p.g = 1 → p.κ = 83 / 200 →
    ∀ {c : ℚ}, 0 ≤ c → c ≤ 1 → ∀ {dp dl : List Nat},
      List.Forall₂ (fun e d => Adm p c e d) r.path dp → List.Forall₂ (fun e d => Adm p c e d) r.loop dl →
      dl.sum ≤ dp.sum := by
  intro r hr p hg hκ c hc0 hc1 dp dl hp hl
  have h := List.all_eq_true.mp table_ok r hr
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact race_ok_of_sums hg hκ h.1 h.2 hc0 hc1 hp hl

/-- Negative control: the binding row fails the check at κ = 0.425 (283 -> 285, 117 -> 115). -/
theorem binding_row_fails_0425 :
    (raceTable.head?.map fun r => decide (285 * sFmax r.loop ≤ 115 * sFmin r.path)) = some false := by decide +kernel

end Formal.Cells.RaceTablePS""" % len(rows))
open(OUT, "w").write("\n".join(out) + "\n")
print("rows", len(rows), "records", nrows, "nodes with a non-necessary path (excluded):", len(nonnec), "worst", [(r["node"], k) for k, r in rows[:4]])
