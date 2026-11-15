# MARGINS: one row per build (owner, PROGRAM.md "FIRST since 2026-11-15")

Kept by shard A from the three shards' journals. One row per routed build: its md5, kappa* (the smallest within-die
scatter, at g = 1, at which some admissible delay assignment breaks it), the binding race in research's instance
names, and whether each number is **Lean** (a checked theorem, standard axioms) or **search** (untrusted simulation
or tool output). "w" is the runt filter of H_RUNT(w): w = 20 ps is the owner's headline, w = 0 no filtering.
An upper bound on kappa* is a counterexample (one failing assignment); a lower bound needs either a proof or a
search whose completeness is stated. Newest builds first.

Columns per the owner (PROGRAM.md, 2026-11-15): **kappa_lo** = the largest κ for which the build is PROVED safe
(Lean), **kappa_hi** = the smallest κ at which a failure was FOUND (Lean witness or search). Both at g = 1.

| build | md5 | kappa_lo (proved) | kappa_hi (found) | binding race (research names) | date, source |
|---|---|---|---|---|---|
| gcd_ps_e6bb4aec (THE gcd target) | .bit aa83c8b7a5e6b68e69729131e984c0f4 | **none**: no whole-circuit safety bound. Single races only: 185 storage-feedback races safe to κ = 0.415 under local premises (`RaceTablePS`, B), the 0.44 feedback race safe to 0.41 (`RaceCertPS.race_margin`) | **0.36, Lean** (`Frontier36.not_seqRunt_le20_above36_R`; w ≤ 20 and w = 0; livelock, i.e. a liveness failure); search: correct at 0.35 under that adversary | merge4's arbiter acknowledge C-element `SLICE_X16Y21.A6` reads the fork late (full-width operands); also 0.40 (quiet deadlock, same C-element, Lean `CexX16`) and 0.44 (`ulink_n_falseResult_85` feedback, Lean) | 2026-11-07..10 |
| BAD_xf2_1 (xorshift, research's known-bad) | .fasm f2873d4650eb67cb270ada5c9a403421 | none | **0, search** (w = 0): fails at κ = 0, 0.16, 0.32 | ulink_n7's enable (SLICE_X24Y40.A6 -> latch bits 0/1 pin A2, 20 pips) late: the counter's next value passes the latch (wrong rounds result) | 2026-11-15, A, FOR-RESEARCH A7 |
| item23_xorshift_s10 (board candidate) | .fasm 56434fc43a066c25c397e8f7e4b9d1ea | none | none found (only one race tried: the ulink_n7 enable race, correct to κ = 0.32, search) | — | 2026-11-15, A |
| item25_collatz_s24 (board candidate) | .fasm c6404633c7d2b095a7ff4e7233a11b72 | none | not searched (decoded; correct at mid-band on 6, 7, 27) | — | 2026-11-15, A |

## Builds received from research (research/FOR-FORMAL.md at b976ce821; files on origin/claude/research)
Registered by A 2026-11-15. md5s are of the uncompressed files; each SDF md5 matches the prefix research gives in
FOR-FORMAL.md, so the files are the builds it names. No `.bit` is committed for these: the margin is computed from
the `.fasm` (the bitstream is `fasm2frames` of it); a board run of the build needs the `.bit` md5 added here.
| build | role | kernel MLIR | fasm md5 | sdf md5 | path (research/data/for-formal/) | notes |
|---|---|---|---|---|---|---|
| item25_collatz_s24 (BOARD-QUEUE list item 25) | board candidate | collatz_preeq2.mlir (rewrite proved, FOR-RESEARCH A6) | c6404633c7d2b095a7ff4e7233a11b72 | e001dc27e644e10a14d08a7730daa958 | item25_collatz_s24/ | not yet |
| item23_xorshift_s10 (list item 23) | board candidate | original xorshift | 56434fc43a066c25c397e8f7e4b9d1ea | 2f825834565b3b7e26642ae8dc07f237 | item23_xorshift_s10/ | not yet; the ulink_n7 enable race that breaks BAD at κ = 0 is correct here at κ = 0, 0.16, 0.32 (search) |
| BAD_xf2_1 (xorshift) | known bad (hold race at ulink_n7, FAST_MIN) | no MLIR override listed (original xorshift) | f2873d4650eb67cb270ada5c9a403421 | dc138ea225845c51346e36e95e05b907 | BAD_xf2_1/ | **0** (search, A, 2026-11-15): FAILS at κ = 0, g = 1, w = 0 with only ulink_n7's enable route (A6 -> latch bits 0/1 pin 1, 20 pips) at its fast-corner max and every other arc at its fast-corner min (research's hold vectors). Correct at every uniform corner. Files: tools-A/target/out/BAD_xf2_1_{cls_n7en,bnd_sim,boundary}.json |
| item 27 xorshift (list item 27), item 26 collatz64, nc64_7 / pc64_7 | board candidate / known-bad minimal pair | xorshift_predec.mlir, collatz64_preeq2.mlir (rewrites proved) | no files yet (rebuild from FOR-FORMAL commands) | a9bdac53 / 6982a9d5 / 98809562 / acc06847 (prefixes) | — | not yet |

Not yet measured: any research build other than gcd_ps (xorshift BOARD-QUEUE #28 / item 27, the shortened-select
candidates, collatz items 25 and 26). Shard C's `formal/tools/margin/run.sh` is the tool for them (FOR-RESEARCH C5
asks research for the builds).
