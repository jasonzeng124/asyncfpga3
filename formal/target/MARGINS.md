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
| fcsel3m s20 (collatz, research's NEW board candidate, BOARD-QUEUE item 28 / ## 29) | sdf d86bdde5 (prefix) | none | **pending**: farm a_margin_fcsel3m (seeds 20, 1, 2, 7, 24 + item 25 under the same settings), filed 2026-11-16 03:0x | -- | A |
| fcsel2 s1 (collatz, select links at 2) | sdf 5b538ca5 | none | 0.22 (w 20), 0.21 (w 0), search, checked | `ulink_n_falseResult_3.many.stage[0]` lat.pair[4] (pair[10] at w 0) reads its ctl late | 2026-11-15, C10 |
| fcsel2 s2 | sdf fb1efc41 | none | 0.27, search, checked | same link, lat.pair[12] | C10 |
| fcsel2 s24 | -- | -- | not measured: A's decoder refused it (AFF.ZRST) | -- | C10; decoder fix by A, 2026-11-16 |
| fcsel1 s24 | sdf afab5445 | none | 0.32, search, checked | same link, lat.pair[10] | C10 |
| fcsel1 s1 | sdf 4445b56c | none | 0.31, search, checked | same link, lat.pair[6] | C10 |
| fcsel0 s24 | sdf bb5fbbdb | none | 0.22, search, checked | same link, lat.pair[16] | C10 |
| item26_collatz64_s25 (board candidate) | fasm aded8a8b, sdf 6982a9d5 | none | **0.26** (w 20 and w 0), search, checked | `ulink_n13.lat.pair[6]` reads `ulink_n13.ctl` late (latch enable; nc64_7's link) | 2026-11-15, C8/C9 |
| BAD nc64_7 (collatz64 known-bad) | fasm 5a196ea0, sdf 98809562 | none | **0.05** (w 0), 0.31 (w 20), search, checked | `ulink_n13.lat.pair[2]` reads `ulink_n13.ctl` late; at w 20 `ulink_n14__1.many.stage[1].u.ctl` | C8/C9 |
| pc64_7 (nc64_7's good neighbour, minimal pair) | fasm 2e7829c0, sdf acc06847 | none | 0.39, search, checked (quiet deadlock) | `ulink_n_falseResult_7.many.stage[0].u.ctl` own feedback | C8/C9 |
| item27 xorshift (board candidate) | fasm a7d9b19f, sdf a9bdac53 | none | none up to 0.45 (1,199 storage-LUT pins, research's 4 hold vectors, w 20 and 0), search | -- | C7 |
| item25_collatz_s24 (board candidate) | fasm c6404633, sdf e001dc27 | none | none admissible at w 20; **0.42 at w 0**, search, checked (703 -> 70) | `ulink_n_falseResult_3.many.stage[0].u.lat.pair[12]` (and 8/10/16) reads that stage's ctl late | C6/C9 |
| item23_xorshift_s10 (board candidate) | fasm 56434fc4, sdf 2f825834 | none | none up to 0.45 (1,239 pins, hold vectors), search | -- | C6; A (ulink_n7 enable race correct to 0.32) |
| BAD_xf2_1 (xorshift known-bad) | fasm f2873d46, sdf dc138ea2 | none | **0**, search (A by hand, C's tool unaided) | ulink_n7's latch bits 0/1 read its enable (SLICE_X24Y40.A6, 20-pip route) late | 2026-11-15, A7, C6 |
| gcd_ps_e6bb4aec (THE gcd target) | .bit aa83c8b7a5e6b68e69729131e984c0f4 | **none**: no whole-circuit safety bound. Single races only: 185 storage-feedback races safe to κ = 0.415 under local premises (`RaceTablePS`, B), the 0.44 feedback race safe to 0.41 (`RaceCertPS.race_margin`) | **0.36, Lean** (`Frontier36.not_seqRunt_le20_above36_R`; w ≤ 20 and w = 0; livelock); 0.40 finite (Lean `CexX16`; C's tool re-finds it) | `ucontrol_merge4.uarb1.ua2` (SLICE_X16Y21.A6) reads `ucontrol_merge4_f` late; also 0.44 (`ulink_n_falseResult_85` feedback, Lean) | 2026-11-07..10; C6 |

Reading (A, 2026-11-16): every kappa_hi below gcd_ps's 0.40 is on a collatz-family build, and in every one the binding
race is the same kind: a link's latch bits seeing that link's own controller (the enable) late. Shortening the select
links (nl6s0-2) moved item 25's binding race from 0.42 (w 0 only) to 0.21-0.32 at the same link
(`ulink_n_falseResult_3` stage 0), not at the select muxes. "Search, checked" = the margin tool's single-pin adversary
(one route slow at (1+κ)·FAST_MAX, all else (1-κ)·FAST_MIN, corner 0, g = 1, 3-4 vectors), failure re-run and accepted
by two independent checkers. It is an upper bound only; no build has a kappa_lo.

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

Measured since (2026-11-15/16, shard C's margin tool `formal/tools/margin/run.sh`): see the table above. Its own
outputs: `formal/tools/margin/out/farm_<build>/`.
