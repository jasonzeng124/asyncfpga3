# MARGINS: one row per build (owner, PROGRAM.md "FIRST since 2026-11-15")

Kept by shard A from the three shards' journals. One row per routed build: its md5, kappa* (the smallest within-die
scatter, at g = 1, at which some admissible delay assignment breaks it), the binding race in research's instance
names, and whether each number is **Lean** (a checked theorem, standard axioms) or **search** (untrusted simulation
or tool output). "w" is the runt filter of H_RUNT(w): w = 20 ps is the owner's headline, w = 0 no filtering.
An upper bound on kappa* is a counterexample (one failing assignment); a lower bound needs either a proof or a
search whose completeness is stated. Newest builds first.

| build | md5 (.bit) | kappa* at g = 1, w = 20 | w = 0 | binding race (research names) | upper end | lower end | date, source |
|---|---|---|---|---|---|---|---|
| gcd_ps_e6bb4aec (THE gcd target, BOARD-QUEUE #4) | aa83c8b7a5e6b68e69729131e984c0f4 | in (0.35, 0.36] | in (0.35, 0.36] | merge4's arbiter acknowledge C-element (`SLICE_X16Y21.A6`) reads the fork late; with full-width operands (wide pairs only, e.g. (0x49e9c618, 0x35bf992e)) the run livelocks: 140 nodes oscillate with period 79 ps, out0 never rises | **Lean**: `Formal.Target.Frontier36.not_seqRunt_le20_above36_R` (every w ≤ 20, g ≥ 1, κ ≥ 9/25, every reset ≥ 400 ns; audit CONFIRMED) | **search only**: this adversary is correct at 0.35 on 60 pairs (B, single-pin and class adversaries); no proof of any lower bound. B's `RaceTablePS` proves 185 storage-feedback races safe up to κ = 0.415 under their local premises (Lean), which does NOT cover the binding (non-feedback) race | 2026-11-09/10, JOURNAL.md, JOURNAL-B.md |
| (same build, second race) | | 0.40 | 0.40 | merge4 ack C-element reads the fork late: quiet deadlock | **Lean**: `Formal.Cells.CexX16.not_netCorrectSeqRunt20` (audit T47) | — | 2026-11-08, JOURNAL-B.md |
| (same build, feedback race) | | 0.44 | 0.44 | `ulink_n_falseResult_85` stage 0, C-element `SLICE_X32Y45.A6` feedback route at the top of its window | **Lean**: `Formal.Target.FrontierRuntR.not_seqRunt_le20_above44_R` (two independent proofs, A and C) | **Lean** for this race alone: safe for κ ≤ 0.41 (`RaceCertPS.race_margin`, B) | 2026-11-07 |

Not yet measured: any research build other than gcd_ps (xorshift BOARD-QUEUE #28 / item 27, the shortened-select
candidates, collatz items 25 and 26). Shard C's `formal/tools/margin/run.sh` is the tool for them (FOR-RESEARCH C5
asks research for the builds).
