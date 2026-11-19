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

**2026-11-19:** the first proved kappa_lo entries (B15-B17): ONE race per build (the output capture), Lean with stated premises; not a whole-build kappa_lo.

| build | md5 | binding race (research names) | race in ps (paths from the split, slack at nominal SDF, research rule row) | kappa_hi (search key) | kappa_lo (proved) | date, source |
|---|---|---|---|---|---|---|
| **spmv s4** (suite11/32, PASS in research's table) | sdf f52af15f | host-write ADDR setup on the row array's `umem0` (RAMB18_X2Y33): host request (SLICE_X22Y92.BQ) -> CLKARDCLK via the 6-LUT umem0 usetup chain vs the ADDR payload (1 LUT + 2.39 ns routing) | min ADDR setup margin **22 ps** over 128 draws (beyond prjxray's widest setup); static mid-band slack +258 ps; **guarded -890 ps** (GUARD_LO 0.772 / GUARD_HI 1.155; failing if_loop_1 s1 -1108, its fix -63) | none found (128 / 128 pass; 95 % upper failure bound ~2.9 % at this model) | none | 2026-11-19, C64 (search: simulation + static sums) |
| if_loop_1 s1, before / after research's RAM guard | sdf b2ad5a7b / c3113cc4 | host-write WE setup on a RAM (C60) | WE setup margin -98 ps worst (fails 3 / 128) / **+1.33 ns** (32 + 32 pass); guarded sums -1108 / -63 ps | b2ad5a7b fails in simulation | none | 2026-11-19, C60 / C63 (search) |
| suite12 (flow v8, ring fusion default) as it lands: straight s1, sqrtsub s1 | sdf 524c6161 / 33ec83be (SAME) | output capture only | -- | none (8 + 8 draws each, 0 pulses) | **0.260 / 0.239** (Lean, one race; B16 bound) | 2026-11-19, B19 (in progress) |
| ringfuse1 (BDC_RING_FUSE=2): xorshift s1-8, collatz s1-8, countloop s1-6, ipow s1-8 (29 routes, sdf SAME) | B18 table | output capture only | -- | none (8 + 8 draws each; ipow s7 pulse bursts in 4 / 16, start-up X) | 0.021-0.352 per route; collatz s2 none (-0.012) (Lean, one race; B16 bound) | 2026-11-19, B18 |
| **board items 38-41** (automatic: ipow s2 81bbe268, collatz s6 c56def07, collatz64 s5 9585dde4, xorshift s8 3497ca67) | sdf as listed | OUTPUT CAPTURE race only: out0_data's whole cone vs out0_req's chain, both from the launching join (worst: umux*.uj*) | request >= A + 1.31-2.32 ns (corner 0), data <= A + 1.04-1.36 ns (B16) | -- | **first proved kappa_lo (one race): xorshift 0.117, collatz 0.281, collatz64 0.108, ipow 0.169** (Lean: SettleAll.settle_all, ChainHold.chain_hold; premises: the cone's roots hold, mux exclusivity, capture at out0_req's rise, H_DECODE) | 2026-11-19, B16 |
| headline routes, output-capture race (farm b_os2, 38 non-array routes) | sdf SAME as research's | as above | B16 table | -- | per-kernel worst: branchloop 0.037, cmpchain 0.150, divmodu 0.246, fold64 0.478, nested 0.133, quadrec 0.387, straight 0.186, twoloops 0.049; **no proof** on gcd 2/3, iterative_division 2/4, iterative_sqrt 4/4 (a long mux data path at the extremes; every draw still passes) | 2026-11-19, B16 |
| test_divui with research's divsize fix (seeds 1 / 2 / 3 / 6 / 7, lines 332 / 386 / 338 / 348 / 516) | sdf ecbc22cc / 96c7d776 / 14c880c4 / 20c9d09e / baf58131 | divider capture (enable chain vs line) | R 91.4 vs D 93.6 ns at corner 0 on seed 1 | none found: 8 / 8 + 8 / 8 slow-carry draws pass each (search) | **none on seed 1 (-0.012)**, 0.082 / 0.006 / 0.037 / 0.180: the fixed rule sizes the line where every arc at its extreme just balances (B17) | 2026-11-19, B17 |
| test_divui, line 528 | sdf 2e6ac4e7 | output capture through the divider (`udivui0`) | request 149.2 / 352.8 ns vs data 91.4 / 215.5 ns | -- | **0.240** (Lean, one race; B15) | 2026-11-19, B15 / B17 |
| **test_divui** automatic (suite10b s1, UDIVUI0 = 5; s2 UDIVUI0 = 6) | sdf 9875e724 / 8ca1bfa7 | **FAILS every draw**: the divider's stage-enable chain `tp[0..256]` (256 kept LUT2s, DIV_TAP 8 x 32) vs the request line `udivui0.udly`; quotient bit 0 is final only after `tp[256]` + the last stage | structural: the line needs about as many LUT hops as the enable chain; on the UDIVUI0 = 528 placement s = 0.5078 (268 elements) passes, 0.5 (264) fails (B12); research's rule saw the quotient settle ~3.4 ns after the operand | not a kappa question: 0 / 8 + 0 / 8 slow-carry draws fail (search); control UDIVUI0 = 528 (sdf 2e6ac4e7) 4 / 4 + 4 / 4 pass | none | 2026-11-19, B12 (untrusted simulation) |
| cmpchain muxsel routes (research's N-way mux select race; s2 it5 line 1, s3 it2 line 1, s2 it5 line 7) | sdf 1c13ff02 / 1994ab81 / a44b35aa | `umux0` select decode `sel[k] = ctl_req & (s == k)` (4 LUTs) pulses while the select line `ULINK_N63__0` is 1 element; answers stay right (exclusive-branch mux) | B13: line 1, draws 20001 / 20002: 12 runts < 1 ns on exactly the four decode LUTs, narrowest 129-692 ps (research's fid GLS: 226-786 ps, same LUTs); line 7: none in either simulator | no wrong answer found: 8 / 8 + 8 / 8 slow-carry draws pass on all three (search); the runts are the finding | none | 2026-11-19, B12 note + B13 |
| research's headline (38 of 62): 33 of its routes in formal's simx (B14; farm b_hl1-4: branchloop 1-4, cmpchain 2 / 3 + the muxsel routes, fold64 2-4, iterative_division 2-4, iterative_sqrt 1-4, nested, quadrec, twoloops, divmodu, straight, gcd, ...) | research's sdf md5 on every route | none found except test_divui (above) | -- | every route research counts as passing passes: 16 / 16 + 16 / 16 slow-carry draws (8 + 8 for gcd) (search); outside formal's simx: 15+ array kernels, factorial (DSP cascade), test_int16 | none | 2026-11-19, B14 |
| item 33 xorshift (fr4a, seed 27: item 27 + uxori1/2 5, umux3 9, ucmpi0 10, uaddi0 12) | sdf 7f0c0592 | pending | pending | pending | none | research FOR-FORMAL 9776b246 |
| item 32 collatz64 (h4s3p, seed 22; ULINK_N13_UACK kept at 3 after C8/C9) | sdf 842dd4d7 | `ulink_n13.lat.pair[4]` vs `ulink_n13.ctl` (kernel race, as items 26/28); ulink_n28 not broken up to 0.45 | enable 1,752 ps at research SDF (routing 1,600) vs data 5,613: **+3,861 ps at SDF**, +987 worst in-band (C18) | first finite failure as above (search); hangs from 0.44 | none | research FOR-FORMAL 2026-11-16 |
| item 31 collatz (nl6s3a, seed 20: item 28 + uselect0 16 -> 7, uaddi0 12 -> 9) | sdf 7aefc4bd | uselect0 capture holds to 0.45; falseResult_7 st0 ctl own feedback | falseResult_7 ctl +174 ps worst in-band, +764 at SDF (C15) | see C15 | none | same |
| item 30 collatz64 (h4s3, seed 10; select links 3/6/3) | sdf 637ff02e | no finite failure up to 0.45 (either host) | falseResult_7 ctls +838 ps at SDF (C18) | none <= 0.45; livelock 0.44 (12 ns host), hangs from 0.41 | none | same |
| item 29 ipow (h4s3m, seed 19; select links 3/3/3/3, mux delays 6/8/7/4 by rule M; replaces h4s3 sdf 4a92cdf3) | sdf b521630f | NOT ANALYSED: A's decoder refuses DSP48E1 sites (no DSP model) | -- | -- | none | same |
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

**Audit T124b (accepted):** the ps slacks in this table are over the arrivals of 3 vectors (operand bits <= 17), not over
all bits. Over all 32 bits, at FAST_MIN: fcsel0 s24 177 ps; item 28's smallest is an input race of 771 ps (bit 19),
below its ulink_n13 race (929 ps in the audit's rule H).

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

## 2026-11-18 (A, from shard B's B8 / B9 / B10): research's automatic-path board items 38-41
Untrusted simulation (formal's simx on the builds' own bits, research's draw model). No kappa_lo for any of them; the
"binding race" column is the line that bounds shortening, from B's linescale on ONE placement (not a buildable circuit).
| item | kernel | sdf md5 (prefix) | draws as built | binding race / tightest line | source |
|---|---|---|---|---|---|
| 38 | ipow | 81bbe268 | every draw passes (B8) | entry compare ucmpi0 (0.75 of built length needed), loop compare ucmpi2 (0.25); DSP48 in no band class of either draw model (B10) | B8, B9, B10 |
| 39 | collatz | c56def07 | every draw passes (B8) | entry compare ucmpi0 n == 1 (0.5); shortening it to 7 FAILS on a rebuild (entry-compare steer 318 / 41 ps with runts, B7's race) | B8, B9 |
| 40 | collatz64 | 9585dde4 | every draw passes (B8) | ucmpi0 n == 1 (0.5), ucmpi2 (0.25), 3n+1 (0.5) | B8, B9 |
| 41 | xorshift | 3497ca67 | every draw passes (B8) | loop compare ucmpi1 (0.75), entry ucmpi0 (0.25) | B8, B9 |
Loop-steer settle >= 1.28 ns with no runts on all four as built (B8). Shard A's rewrite work today (A19-A21) does not
change these builds.

## 2026-11-18 21:4x (A, from shard B's B9 cut A/B and B11): shortened automatic builds and the NOT CLEAN suite routes
Untrusted simulation (formal's simx on the builds' own bits; research's draw model: 32 draws + 32 slow-carry draws). No
kappa_lo for any of them. "Cut" = the lines B9's linescale found unneeded set to 0 (or half), compares kept as built,
rebuilt and re-placed (not a what-if).
| kernel | seed | as built: sdf, last answer | cut: sdf, last answer | change | all checks on the cut | source |
|---|---|---|---|---|---|---|
| collatz (item 39 sizes) | 6 | c56def07, 31.64 us | 76a0d09d, 26.12 us | -17.4 % | pass; NEARMISS 7 / 13 (ulink_n26 latch data) | B9 |
| collatz | 1 | 30fdadfa, 29.78 us | 79a35ac0, 24.15 us | -18.9 % | pass; NEARMISS 7 / 13 (same latch) | B9 |
| collatz | 2 | d863eac9, 31.22 us | cfbd9baa, 24.64 us | -21.1 % | pass; NEARMISS 0 | B9 |
| collatz, entry compare also cut (UCMPI0 7) | 6 | - | (lsj) | FAILS: 2 wrong, 15 hung of 32 | entry-compare steer 318 / 41 ps with runts (B7's race) | B9 |
| collatz64 (item 40) | 5 / 1 / 2 | 9585dde4 100.20 / 6333dd2d 101.27 / 1e34ade0 104.48 us | 27c5d16f 86.94 / 7af7feb2 85.31 / d33e28ec 90.51 us | -13.2 / -15.8 / -13.4 % | pass; NEARMISS 440 in one draw on seed 5 (latch data), else 0 | B9 |
| ipow (item 38) | 2 | 81bbe268, 4.72 us | 89987a1c, 3.85 us | -18.5 % | pass; NEARMISS 0; DSP48 in no band class (B10) | B9, B10 (seeds 1 / 3 there) |
| ipow | 3 / 4 | 58417727 4.504 / c146105a 4.682 us | bcc04b6d 3.813 / 86ccfb48 3.999 us | -15.3 / -14.6 % | pass (B10; slow-DSP pattern repeats) | B10 |
| xorshift (item 41) | 8 | 3497ca67, 38.49 us | 8e1a90d4, 36.46 us | -5.3 % | pass; NEARMISS 3 in one draw (latch data) | B9 |
Three seeds for collatz and collatz64 is below the 4-seed rule (ipow now has seeds 1-4, B10); B's farm b_lsj (seeds 1-8) is queued.
B11 (research's flow-v6 suite column, the 13 routes its rule called NOT CLEAN; sdf identical to research's on every one):
every route 32/32 draws + 32/32 slow-carry, and 8/8 + 8/8 with the loop counter preloaded near the carry where the
kernel has one. sdf prefixes: countloop 97dda2e9 / 526cfe59 / 54082d7e, sqrtsub 77f952f2, varshift ae9d045b, brhash
2744d342 / 294cbf1d / 680befc8 / caa607d6, lfsrfind 88fb2e5b / a111a4e3, horner 0bc03e6f, isprime 4efc0f0d (flow v5).
Plainly: none of research's NOT CLEAN rows turned into a failure in formal's model; formal's simx is not the board.

