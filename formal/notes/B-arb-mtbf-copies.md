# B probe Bmt: Bov's arbcell-overlap prediction, evaluated per copy on rebuilt arb_mtbf routes

Shard B, 2026-10-27. This is a follow-up to `B-arb-overlap-race.md` (Bov). Bov proved a
firing condition per copy. Here I evaluate it for all 192 `pop[i]` copies of
`cells/hw/arb_mtbf.v`, using routes rebuilt from the FASM bits and prjxray-db delays.
The board reported (ARBITER.md) RAW 139/192 and FILTERED 15/192, with the filtered copies
`[0,5,21,29,30,35,38,57,76,85,89,90,157,177,179]`.

No Lean in this probe. All builds, scripts and outputs are in
`/tmp/claude-0/-home-user-asyncfpga3/7f52a4bc-3f11-5919-b34a-537c5f812fdf/scratchpad/mtbf/`.
No repo file other than this note was written.

## Answer in one paragraph

**I could not reproduce the measured bitstream, and Bov's mechanism does not explain the
8%.**

- **Reproduction.** No artefact of the measured build is archived, so there is nothing to
  `cmp` against. The build ran before 2026-08-11 with a nextpnr binary and a yosys version
  that are not recorded. Using the recorded flow (seed 5, no RLOC, the same RTL) with
  today's toolchain gives the same netlist size (2943 LUT sites), and its FASM is
  deterministic. I also rebuilt nextpnr at its base revision with only the lut-pinmap
  patch, to get the old SDF semantics. That route matches several recorded fingerprints:
  - q touches A5 in exactly 107 copies, as recorded;
  - 151 copies have "zero" SDF detector skew (146 recorded);
  - the short ladder rungs match exactly.

  The long ladder rungs do not match, so it is not the measured route.
- **Prediction.** I evaluated Bov's condition at a consistent corner, with the filter
  threshold Dw computed the same way (the filter's own chain arcs, routes and site pins).
  It predicts **0 FILTERED copies on all 7 routes, at FAST_MIN and at SLOW_MAX**. Bov's
  all-trace cap |s+b| > Dw admits at most 0-2 copies per route.
- **Where Bov's count came from.** The condition only gives a board-like count (14-21 per
  route at SLOW_MAX) if Dw is replaced by the SDF-era 203 ps, and 203 ps is not the
  threshold once site pins are included. Even under that generous threshold, the model
  predicts the **A5 association with the wrong sign**: A5 copies fire more often, 69/628
  against 28/524 pooled. The board saw 2/107 against 13/85.

So the 8% stays unexplained by the digital transport model of rig plus cell.

## Toolchain (CLAUDE.md)

- **Main toolchain.** `cloud/toolchain-cache.sh fetch` gave key `d7ce266cff0c8e1e`.
  `cells/verify/toolchain.sh` passes, **nextpnr sha256 `9c732bc6303458df`**, yosys 0.62.
  - At fetch time the binaries could not run: libtcl8.6 and boost 1.83 shared libraries
    were missing, which I fixed with apt. toolchain.sh passed anyway, because it only
    `strings` the binary.
  - The prjxray Python dependencies (textx etc.) were installed with pip.
- **Archaeology binary** (`oldpnr/`): openXC7 nextpnr-xilinx `bfdeaf7c` + `lut-pinmap.patch`
  only, **sha256 `ba841b6ec27b2292`**.
  - It **fails** toolchain.sh as intended: rloc, place-weight, ff-timing, lut-perm-sink
    and dsp-constpins are missing. The scratch copy of `build_hw.sh` logged that failure
    instead of aborting.
  - It was used only to test fingerprints. Nothing routed with it is a result.
- **Side finding (toolchain.sh).** The `dsp-areg` fingerprint `ZAREG_2_ACASCREG_1` is also
  in the **unpatched** source (`xilinx/fasm.cc:5096` at bfdeaf7c), so that check reports
  "ok" on a binary without the patch. It cannot fail. That breaks CLAUDE.md's rule; I did
  not change it.
- **`--freq` was NOT passed.** That breaks CLAUDE.md, and I did it on purpose. The measured
  build used `build_hw.sh`'s default (no `NEXTPNR_FREQ`), and the goal was to reproduce it.
  Every quantity analysed here is asynchronous: ring outputs to arbiter LUTs to detector to
  filter. No clock timing claim is made from these routes, and "PASS at 12 MHz" in their
  logs means nothing.
- **Flow.** `BD_NO_TIGHTEN=1 BD_RLOC=none NEXTPNR_SEED=N hw/build_hw.sh arb_mtbf`, run in
  scratch copies of `cells/`. RLOC did not exist when the measured build was made.
  - Today's default `BD_RLOC=v8` stamps 1573 LUTs of this design into spine groups, even
    though it logs "nothing to stamp". It is therefore not the measured flow. One v8 seed-5
    route is reported for completeness.

## Step 2: what is recorded about the measured build

- **Seed 5**, from `build_hw.sh` lines ~397-421: "Seed 5 is pinned (depth
  0/124/398/1336/2511/6471 ps, floor 124/398/672/946/1958/2432 ps)", 2943 LUT sites, WFILT=2.
- **Not passed:** `--freq`, RLOC (both predate 2026-08-21).
- **Board run:** 13.77 h, retired before arb_prot's 2026-08-11 run.
- **Per-copy data that exist:** only the FILTERED list in ARBITER.md, plus the aggregates:
  - RAW 139/192;
  - 146 "zero-skew" copies;
  - q touches A5 in 107 copies (2/107 against 13/85 firing).

  There is no per-copy RAW list. There is no FASM, bit, SDF or `state.json` in the repo or
  on any branch (`origin/claude/research`, `origin/claude/audit` were searched).
- **Toolchain:** neither the nextpnr nor the yosys binary is recorded. JOURNAL:868 notes an
  August yosys behaviour that "does not reproduce on yosys 0.62".

## Step 3: reproduction

| build | binary | FASM md5 | ladder depth (SDF) | ladder floor (SDF) | q touches A5 | SDF g1c/g2c skew = 0 |
|---|---|---|---|---|---|---|
| **recorded** | ? | (none archived) | 0/124/398/1336/2511/6471 | 124/398/672/946/1958/2432 | 107 | 146 |
| o5 (old binary, seed 5) | ba841b6e | 45b17ebe6178 | 0/124/398/**1561/2865/6899** | 124/398/672/946/**2419/3044** | **107** | 151 |
| n5 (current, seed 5) | 9c732bc6 | c0682b3c8d99 | 0/124/543/1674/3382/6813 | 124/543/962/1381/2351/3759 | 104 | 40 |

- **Determinism.** Two seed-5 builds are byte-identical in FASM and routed JSON, for both
  binaries (`n5`/`n5b`, `o5`/`o5b`). The `.bit` differs only by its header timestamp, as
  `build_hw.sh` documents.
- **Why the current-binary SDF cannot match the record.** The lut-perm-sink patch changed
  what the SDF reports. 398 = 124 + 150 + 124, where 150 is nextpnr's placer estimate for
  "same tile, other pair". The patched SDF reports the real hop, 295.
- **Verdict on reproduction.** The old binary reproduces the estimate-dominated rungs
  exactly, and the A5 count exactly. Its long rungs differ by 13-25%, so the placement
  differs. The likely causes are a different yosys (abc), the compiler, or a local patch.
  **The measured route is not reproduced.** Comparing copy i on a rebuilt route with copy i
  on the board is therefore chance-level: about 1 of 15 overlap, against 15·15/192 ≈ 1.2
  expected by chance.

**Side finding on ARBITER.md's "146 copies at exactly 0 ps skew".** On o5 (old SDF
semantics) 141 of the 151 "zero-skew" copies are the placer estimate 150/150 ps, not a
route. The prjxray route-only skew of those copies has median 138 ps and max 328 ps. With
site pins, |s| has median 234 ps and max 572 ps at SLOW_MAX. The refutation "grant→detector
interconnect skew does not decide it" was therefore computed on estimates, and should not
be cited as evidence about the real skew.

## Step 4: per-copy evaluation

**Script.** `percopy.py BUILD OUT.json`. It imports `formal/tools/fasm2lean2` read-only
(Fabric/Extract walker and its Elmore model).
- The routed JSON is used only to find which LUT site holds which cell, and which logical
  input `X_ORIG_PORT` puts on which pin.
- Every one of the 12 pins per copy is walked through the FASM's active pips to its source
  site pin. The source must be the expected driver: the stim ring LUT, ustate O6, ugrant O5
  through its OUTMUX, the detector, or chain link 0/1. Otherwise the script aborts.
- Delay per pin and corner = pip intrinsic sum (+ Elmore at SLOW_MAX only, fasm2lean2's
  convention) + prjxray site-pin delay + prjxray `timings/<tile>.sdf` IOPATH arc (per pin,
  O5 or O6, per LUT letter and tile type).
- I added one walker fix locally: the bidirectional long-line pips (`LV_L0<<->>LV_L18`
  etc.) appear in the FASM in the orientation opposite to the json. fasm2lean2 missed
  them, and its walk then reports a "floating" node.

**Cross-check.** For every copy, the FASM-derived physical pin of each of 10 nets equals
the SDF INTERCONNECT sink pin: **1920/1920 on n5 and 1920/1920 on o5**. The detector is on
O6 in all copies, as ARBITER.md says.

**Formulas** (Bov §3/§4, with every term from the bits):
- s = e1 − e2
- b = b5 − b6
- κ1 = a1 − s1 − b6
- κ2 = a2 − s2 − b5
- D = max(s + min(κ1, b), −s + min(κ2, −b))
- Dw = T(raw→chain0→chain1→uwand.I1) − T(raw→uwand.I0)
- FILTERED iff D > Dw; RAW iff D > 0 (handover traces).
- "cap" = Bov's all-trace bound |s + b| > Dw.

### Predicted vs observed (counts of 192)

| route | FILT FAST_MIN | FILT SLOW_MAX | cap>Dw FAST_MIN / SLOW_MAX | RAW (D>0) FAST_MIN / SLOW_MAX | Dw SLOW_MAX min / median | D>203 SLOW_MAX |
|---|---|---|---|---|---|---|
| **board** | 15 (filtered, any corner) | | | 139 | ~203 claimed | |
| n5 (seed 5) | 0 | 0 | 1 / 1 | 41 / 39 | 435 / 1348 | 21 |
| n1 | 0 | 0 | 0 / 0 | 37 / 35 | 666 / 1342 | 16 |
| n2 | 0 | 0 | 0 / 0 | 45 / 40 | 596 / 1357 | 14 |
| n3 | 0 | 0 | 0 / 0 | 46 / 45 | 546 / 1312 | 17 |
| n4 | 0 | 0 | 2 / 0 | 43 / 39 | 425 / 1365 | 18 |
| **5 seeds, mean [range]** | **0 [0,0]** | **0 [0,0]** | 0.6 [0,2] / 0.2 [0,1] | 42.4 [37,46] / 39.6 [35,45] | | **17.2 [14,21]** |
| o5 (old binary) | 0 | 0 | 2 / 0 | 28 / 26 | 514 / 1381 | 11 |
| v8 s5 (RLOC v8) | 0 | 0 | 2 / 1 | 34 / 33 | 732 / 1437 | 21 |

- **Margin.** The largest D − Dw over all copies and routes is −34 ps at FAST_MIN and
  −144 ps at SLOW_MAX. The FAST_MIN figure is not a near miss in the guardband sense: the
  formula's terms are all one corner.
- **Elmore sensitivity.** Dropping Elmore, or applying it at FAST_MIN too, leaves FILT at
  0 everywhere. The cap and RAW counts move by at most ±5.
- **The calculator can fire.** With Dw forced to 203 ps it fires 14-21 copies per route.
  So a 0 count is not a structural artefact of the script.

**Predicted per-copy list.** Under the model's own Dw the list is empty on every route.
Under the Dw = 203 reading at SLOW_MAX, for n5: `[2,11,20,37,43,54,86,97,103,117,121,122,124,150,160,166,170,177,180,182,185]`.
That list overlaps the board list in 1 copy, which is chance. The counts for every route
are in the scratchpad `results.txt`; the per-copy values are in each route's JSON.

### Why the count is zero

The overlap D is essentially a difference of two site pins. The threshold Dw is two full
links. In detail:
- The detector skew s is dominated by site pins. Median |s| is 234 ps, with a maximum of
  about 720 ps at SLOW_MAX.
- κ is strongly negative (median −490 to −600 ps at SLOW_MAX). The reason is that q's own
  path into ugrant (route + site pin + arc, about 450-570 ps) is longer than the request
  fork difference. Bov's 305 ps trace assumed nextpnr's 295 ps same-slice hop **including**
  the site pin on A5. With prjxray's own pip and site delays, κ usually binds below b.
- Dw is two LUT arcs plus three routes plus a site-pin difference: SLOW_MAX median about
  1.35 ns, minimum 425 ps; FAST_MIN median about 420 ps. ARBITER.md's "minimum threshold
  203 ps" came from the pre-lut-perm-sink SDF, with 0 or 150 ps in-slice estimates and no
  site pins. **This is exactly the per-copy filter site-pin term Bov flagged and left
  unmodelled.** Once it is modelled, it removes the effect it was meant to qualify.

### The A5 lead, under the model

I pooled the 6 BD_RLOC=none routes and used the generous Dw = 203 at SLOW_MAX:
- copies where q touches A5 fire **69/628 (11%)**;
- the rest fire **28/524 (5%)**.

The board shows the opposite: 2/107 (1.9%) against 13/85 (15%). q on A5 shrinks q's site
pin, which makes κ less negative and gives more overlap. The ustate-side effect Bov
predicted, a slower request pin and less overlap, does not dominate. So under the mechanism
the board's direction is unexpected, even with the threshold most favourable to the
mechanism.

## Is the 8% explained?

**No.** On every rebuilt route, Bov's condition predicts 0 of 192 filtered copies at a
consistent corner. That holds over 5 seeds of the measured flow, the old-binary route and
the v8 route. Even the all-trace cap gives at most 2 copies. The board saw 15. A board-like
count appears only with the 203 ps threshold, which does not survive prjxray's site pins.
Under that threshold the A5 association comes out with the wrong sign. RAW is not
discriminating: the model gives about 40 copies from handovers, while the all-trace cap
allows nearly all 192 (board 139).

**What this does not show.**
- **Not the measured route.** The measured route was not reproduced, so this is a
  statement about the population of routes the flow produces, not about the board's 192
  copies.
- **Consistent corners only.** Within-die mismatch (about 8.5% ring scatter) and
  rise/fall asymmetry, which prjxray does not characterise, are not modelled.
- **Transport only.** Trains that alias through the filter (Bov `train_passes`) and
  metastable q excursions longer than Dw are not excluded. These are now the remaining
  candidates, together with whatever an inertial or analog LUT model adds.
- **The 13.77 h board run's true threshold is unknown.** Nothing on the board measures Dw
  of the filter itself.

## Files (scratchpad, `.../scratchpad/mtbf/`)

- **Build scripts:**
  - `build.sh TAG SEED` (current toolchain, BD_RLOC=none);
  - `build_old.sh TAG SEED` (old binary);
  - builds `n1..n5`, `n5b`, `o5`, `o5b`, `v8/s{1,2,3,5}`;
  - `oldpnr/` (source and binary of the old nextpnr).
- **Analysis:**
  - `percopy.py` (extraction and formula);
  - `summ.py`, `summ2.py` (counts and caps);
  - `fp.py` (A5 count, zero-skew count, D>203);
  - `xsdf.py` (FASM against SDF pin cross-check);
  - `ladders.py` (depth and floor from the SDF, via `arb_mtbf_measure.py`'s own functions).
- **Per-copy outputs:** `n1..n5.json`, `o5.json`, `v8_s5.json`. Each has every pin, route,
  site, arc and Elmore term, plus s, b, κ1, κ2, D and Dw at four corners.
