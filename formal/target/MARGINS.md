# MARGINS: one row per build (owner, PROGRAM.md "FIRST since 2026-11-15")

Kept by shard A from the three shards' journals. One row per routed build: its md5, kappa* (the smallest within-die
scatter, at g = 1, at which some admissible delay assignment breaks it), the binding race in research's instance
names, and whether each number is **Lean** (a checked theorem, standard axioms) or **search** (untrusted simulation
or tool output). "w" is the runt filter of H_RUNT(w): w = 20 ps is the owner's headline, w = 0 no filtering.
An upper bound on kappa* is a counterexample (one failing assignment); a lower bound needs either a proof or a
search whose completeness is stated. Newest builds first.

Owner, 2026-11-16 (PROGRAM.md, "A kappa is not a result"): the race in picoseconds leads; kappa stays as the search
key. Columns per the owner (PROGRAM.md, 2026-11-15): **kappa_lo** = the largest κ for which the build is PROVED safe
(Lean), **kappa_hi** = the smallest κ at which a failure was FOUND (Lean witness or search). Both at g = 1.

| build | md5 | binding race (research names) | race in ps (paths from the split, slack at nominal SDF, research rule row) | kappa_hi (search key) | kappa_lo (proved) | date, source |
|---|---|---|---|---|---|---|
| item 32 collatz64 (h4s3p, seed 22; ULINK_N13_UACK kept at 3 after C8/C9) | sdf 842dd4d7 | pending (research wants ulink_n13 / ulink_n28 hold) | pending | pending (C's farm) | none | research FOR-FORMAL 2026-11-16 |
| item 31 collatz (nl6s3a, seed 20: item 28 + uselect0 16 -> 7, uaddi0 12 -> 9) | sdf 7aefc4bd | pending (research wants uselect0's data vs request) | pending | pending (C's farm) | none | same |
| item 30 collatz64 (h4s3, seed 10; select links 3/6/3) | sdf 637ff02e | pending | pending | pending | none | same |
| item 29 ipow (h4s3, seed 19; select links 3/3/3/3) | sdf 4a92cdf3 | pending | pending | pending | none | same |
| **fcsel3m s20 = item 28** (collatz, research's NEW board candidate, BOARD-QUEUE ## 29) | fasm e4f25940, sdf d86bdde5 | `ulink_n13.lat.pair[6]` closes (enable from `ulink_n13.ctl`) vs its next data via `ulink_n13.uack` -> `umux1.uya` -> `ulink_n_falseResult_5` stage 1 -> `umux1.udat.pair[6]`; no select-arrival race below 0.85 (A's selrun) | split at ulink_n13.ctl: enable 607 ps (253 cells + 354 route) vs data 1,950 ps (998 + 952): **slack 1,343 ps** at fast mid, 3,345 at slow mid (A8); **research rule H +1,337 ps** (nominal SDF), hold_bits min 1,566 ps: agree (C, JOURNAL-C 03:52) | **0.42** (w 20 and w 0), search, checked | none | 2026-11-16, A8 |
| fcsel3m s1 / s2 / s24 / s7 (item 28's structure, other seeds) | sdf d7d13c5d / ce8de32a / e2d7c95d / 751c6b81 | `ulink_n_falseResult_3.many.stage[0]` latch pairs vs its ctl (s24 w 0 also `ulink_n10__3`); the latch reads the kernel INPUT bus (A9) | s24: enable +725 ps vs a_ack fall +977 then a zero-hold env's new operand at the bit +1,376: **slack 651 ps**; s7: **917 ps**; a race against the sender's data hold, which the board PS never cuts that short (A9) | 0.41 / 0.37 (0.33 w 0) / **0.27** / **0.28**, search, checked | none | A8 |
| item25 under A8's run (same settings, same request) | sdf e001dc27 | as below | pending | none admissible (w 20); 0.42 (w 0) | none | A8 |
| fcsel2 s1 (collatz, select links at 2) | sdf 5b538ca5 | `ulink_n_falseResult_3.many.stage[0]` lat.pair[4] (pair[10] at w 0) reads its ctl late | pending | 0.22 (w 20), 0.21 (w 0), search, checked | none | 2026-11-15, C10 |
| fcsel2 s2 | sdf fb1efc41 | same link, lat.pair[12] | pending | 0.27, search, checked | none | C10 |
| fcsel2 s24 | -- | -- | pending | not measured: A's decoder refused it (AFF.ZRST) | -- | C10; decoder fix by A, 2026-11-16 |
| fcsel1 s24 | sdf afab5445 | same link, lat.pair[10] | pending | 0.32, search, checked | none | C10 |
| fcsel1 s1 | sdf 4445b56c | same link, lat.pair[6] | pending | 0.31, search, checked | none | C10 |
| fcsel0 s24 | sdf bb5fbbdb | same link, lat.pair[16] | **616 ps** at fast mid, data from the kernel input bus (A9: zero-hold sender race) | 0.22, search, checked | none | C10 |
| item26_collatz64_s25 (board candidate) | fasm aded8a8b, sdf 6982a9d5 | `ulink_n13.lat.pair[6]` reads `ulink_n13.ctl` late (latch enable; nc64_7's link) | split at `ulink_n13.ctl`: enable 961 ps (242 cells + 719 route) vs data 2,170 ps via n13.uack, umux1.uya, falseResult_5 stage 1, umux1.udat: **slack 1,209 ps** fast mid, 3,240 slow mid (A9) | **0.26** (w 20 and w 0), search, checked | none | 2026-11-15, C8/C9 |
| BAD nc64_7 (collatz64 known-bad) | fasm 5a196ea0, sdf 98809562 | `ulink_n13.lat.pair[2]` reads `ulink_n13.ctl` late; at w 20 `ulink_n14__1.many.stage[1].u.ctl` | pending | **0.05** (w 0), 0.31 (w 20), search, checked | none | C8/C9 |
| pc64_7 (nc64_7's good neighbour, minimal pair) | fasm 2e7829c0, sdf acc06847 | `ulink_n_falseResult_7.many.stage[0].u.ctl` own feedback | pending | 0.39, search, checked (quiet deadlock) | none | C8/C9 |
| item27 xorshift (board candidate) | fasm a7d9b19f, sdf a9bdac53 | -- | pending | none up to 0.45 (1,199 storage-LUT pins, research's 4 hold vectors, w 20 and 0), search | none | C7 |
| item25_collatz_s24 (board candidate) | fasm c6404633, sdf e001dc27 | `ulink_n_falseResult_3.many.stage[0].u.lat.pair[12]` (and 8/10/16) reads that stage's ctl late | w 0 race is at the kernel INPUT (data from a_data): **1,193 ps** fast mid, 2,931 slow mid, against a zero-hold sender (A9) | none admissible at w 20; **0.42 at w 0**, search, checked (703 -> 70) | none | C6/C9 |
| item23_xorshift_s10 (board candidate) | fasm 56434fc4, sdf 2f825834 | -- | pending | none up to 0.45 (1,239 pins, hold vectors), search | none | C6; A (ulink_n7 enable race correct to 0.32) |
| BAD_xf2_1 (xorshift known-bad) | fasm f2873d46, sdf dc138ea2 | ulink_n7's latch bits 0/1 read its enable (SLICE_X24Y40.A6, 20-pip route) late | pending | **0**, search (A by hand, C's tool unaided) | none | 2026-11-15, A7, C6 |
| gcd_ps_e6bb4aec (THE gcd target) | .bit aa83c8b7a5e6b68e69729131e984c0f4 | `ucontrol_merge4.uarb1.ua2` (SLICE_X16Y21.A6) reads `ucontrol_merge4_f` late; also 0.44 (`ulink_n_falseResult_85` feedback, Lean) | pending | **0.36, Lean** (`Frontier36.not_seqRunt_le20_above36_R`; w ≤ 20 and w = 0; livelock); 0.40 finite (Lean `CexX16`; C's tool re-finds it) | **none**: no whole-circuit safety bound. Single races only: 185 storage-feedback races safe to κ = 0.415 under local premises (`RaceTablePS`, B), the 0.44 feedback race safe to 0.41 (`RaceCertPS.race_margin`) | 2026-11-07..10; C6 |

**Hangs the frozen statement cannot see (C, 2026-11-16 04:08; search):** partial-acknowledge hangs at
`ulink_n_falseResult_7` stage 0 ctl reading its own output late: fcsel1 s24 from kappa 0.09 (w 20), item 28 0.36,
item 26 0.37, item 27 0.28 (steer cones elsewhere). Spec.Env is unsatisfiable there (SpecWF.env_unsat_partial_ack),
so they are not in the kappa_hi column; under the proposed SpecWF they are counterexamples. Picosecond form pending (C).

Reading (A, 2026-11-16, reworded after the owner's "A kappa is not a result"): on every collatz-family build the race
the search breaks first is one kind: a link's latch bits seeing that link's own controller (the enable) late. A
kappa says only which race the adversary breaks first; it is not a measured margin and builds are not ranked on it
here. "Search, checked" = the margin tool's single-pin adversary (one route slow at (1+κ)·FAST_MAX, all else
(1-κ)·FAST_MIN, corner 0, g = 1, 3-4 vectors), failure re-run and accepted
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
