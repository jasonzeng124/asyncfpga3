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

## Builds received from research (research/FOR-FORMAL.md at b976ce821; files on origin/claude/research)
Registered by A 2026-11-15. md5s are of the uncompressed files; each SDF md5 matches the prefix research gives in
FOR-FORMAL.md, so the files are the builds it names. No `.bit` is committed for these: the margin is computed from
the `.fasm` (the bitstream is `fasm2frames` of it); a board run of the build needs the `.bit` md5 added here.
| build | role | kernel MLIR | fasm md5 | sdf md5 | path (research/data/for-formal/) | kappa* |
|---|---|---|---|---|---|---|
| item25_collatz_s24 (BOARD-QUEUE list item 25) | board candidate | collatz_preeq2.mlir (rewrite proved, FOR-RESEARCH A6) | c6404633c7d2b095a7ff4e7233a11b72 | e001dc27e644e10a14d08a7730daa958 | item25_collatz_s24/ | not yet |
| item23_xorshift_s10 (list item 23) | board candidate | original xorshift | 56434fc43a066c25c397e8f7e4b9d1ea | 2f825834565b3b7e26642ae8dc07f237 | item23_xorshift_s10/ | not yet; the ulink_n7 enable race that breaks BAD at κ = 0 is correct here at κ = 0, 0.16, 0.32 (search) |
| BAD_xf2_1 (xorshift) | known bad (hold race at ulink_n7, FAST_MIN) | no MLIR override listed (original xorshift) | f2873d4650eb67cb270ada5c9a403421 | dc138ea225845c51346e36e95e05b907 | BAD_xf2_1/ | **0** (search, A, 2026-11-15): FAILS at κ = 0, g = 1, w = 0 with only ulink_n7's enable route (A6 -> latch bits 0/1 pin 1, 20 pips) at its fast-corner max and every other arc at its fast-corner min (research's hold vectors). Correct at every uniform corner. Files: tools-A/target/out/BAD_xf2_1_{cls_n7en,bnd_sim,boundary}.json |
| item 27 xorshift (list item 27), item 26 collatz64, nc64_7 / pc64_7 | board candidate / known-bad minimal pair | xorshift_predec.mlir, collatz64_preeq2.mlir (rewrites proved) | no files yet (rebuild from FOR-FORMAL commands) | a9bdac53 / 6982a9d5 / 98809562 / acc06847 (prefixes) | — | not yet |

Not yet measured: any research build other than gcd_ps (xorshift BOARD-QUEUE #28 / item 27, the shortened-select
candidates, collatz items 25 and 26). Shard C's `formal/tools/margin/run.sh` is the tool for them (FOR-RESEARCH C5
asks research for the builds).
