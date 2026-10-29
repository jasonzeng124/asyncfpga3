# ring128 at the distribution level (ring128_summary, soft), 2026-10-29

ring128 (hard) is BLOCKED: the August per-ring data and route are gone. What is on record is the
per-length summary of ratio = measured / predicted, where predicted = 2 x loop in **that route's
nextpnr SDF** (cells/hw/README.md:297-301, 309, 322-323, 353). `cells/gls/fid/ring128_summary.py`
runs a summary-level version of the check today. It rebuilds the route, models every ring, and summarises the
model's ratio the way `hw/ro_many_measure.py` summarises the board: its `pct()` nearest rank,
`kfit` through the origin, "slower than the scaled model" = residual (m - kfit p)/m > 0, and
its two-parameter fit. The board numbers come only from the README. No output of this script is
used as an oracle.

**This compares across routes.** The August route cannot be rebuilt, so this tests the SHAPE of
the population: its level, its width per length, the 7-vs-63 length dependence and the slow
fraction. It never tests a ring.

## What was built

8 routes of `hw/ro_many_top.v`, `cd cells && BD_NO_TIGHTEN=1 BD_RLOC=none [NEXTPNR_SEED=s]
hw/build_hw.sh ro_many_top`. BD_RLOC=none is the only way to reproduce a pre-08-21 route. As in
August, no --freq was given: the rings are unclocked and only the readback is clocked. The toolchain
was nextpnr-xilinx sha256 9c732bc6303458df, with all `verify/toolchain.sh` fingerprints ok,
including lut-perm-sink. Each build is about 1 minute. The default seed reproduces F1's rebuild byte
for byte (json 0f22d385, sdf 28248a69), and `ring_predict.py` on it equals `f1_rings_ro_many_top.tsv`
exactly. xray SDF: `xray_delay.py`, prjxray-db zynq7 rev 0a0added.

| seed | routed.json | nextpnr sdf | xray.sdf | .bit |
|---|---|---|---|---|
| default | 0f22d3851ad5 | 28248a6973fb | 3fb582274ae4 | 9ad0bf356391 |
| 1 | 47568f6cd484 | c5e26a2df139 | 1d4acf4b7d54 | cd3de238e2b6 |
| 2 | 819c33cff7ac | b431e157e628 | 03e1d881ec88 | e15e3d51e0c7 |
| 3 | 991d9df124c3 | c010bc240bdc | c57e79d008e5 | f15b36c40353 |
| 4 | cca7890669f8 | a6a3aabc664d | 465e55986402 | 6eadb2afe7a7 |
| 5 | 53d2017ed66d | 38e983b7deef | 8f558d69780e | c12e2406c9b4 |
| 6 | 31928675b0e1 | cc38e9b6829f | bdefeaae9f6b | 4c17098529ba |
| 7 | 19a38dc24506 | e5dea3f18984 | 2b70da0e06ce | 32b80f84af85 |

All 8 routes passed build_hw.sh (fasm_audit PASS, 4543 LUT sites). The .bit md5s include a header
timestamp.

## The three periods per ring

* **P_np**: 2 x loop in the route's nextpnr SDF. This is today's patched binary.
* **P_pre**: P_np with every INTERCONNECT into a LUT pin the route reached through a permutation pip
  (3625-3662 of 3840 in-ring arcs per route) replaced by the placer estimate that the
  pre-lut-perm-sink binary wrote there. Per `patches/README.md`, that estimate is 0 ps on the same LUT
  site, 150 ps in the same tile, and 450 + 90|dy| + 45|dx| otherwise, using prjxray tile-grid coordinates.
  **August's SDF came from that binary** (inventory.json ring128 provenance: built 08-23, the patch
  landed 09-20), so P_pre, not P_np, is the like-for-like denominator. **It is an emulation built
  from the patch's description, not a run of the old binary.** Two parts of it are inferred:
  1. "same LUT pair", read as the same site and the same LUT letter;
  2. dx/dy in prjxray grid units.

  A cross-route check against ro_top (rebuilt today, json 9c37e02c, sdf 18fca28e) and the two August
  pre-patch ro_top SDFs on record (inventory ring5_a/b aug_sdf_ps):

  | links | today P_np | today P_pre (emulated) | Aug SDF route A | Aug SDF route B |
  |---|---|---|---|---|
  | 7 | 7264 | 5944 | 8290 | 4674 |
  | 15 | 14786 | 12368 | 13576 | 12008 |
  | 31 | 33024 | 31890 | 24842 | 28228 |
  | 63 | 60496 | 52504 | 56784 | 55548 |
  | 127 | 122384 | 112178 | 103418 | 112972 |

  P_np is above both August SDFs at 15, 63 and 127 links. P_pre sits inside or near their range. This
  supports the direction of the emulation, but only across routes. Its LEVEL is not pinned: at 127
  links the two August routes alone differ by 9%.
* **P_model**: the full stack. `xray.sdf` is read by gen.py's own `read_sdf` at `GLS_SDF_FIELD=band`
  0.38, with `GLS_SCATTER_REGION=0.16` (10x10 slices) + `GLS_SCATTER=0.126` `GLS_SCATTER_MODE=wire`,
  seeds 1..16. This goes through `fid/f3/ring_scatter.py`'s `periods()` and is not a
  re-implementation.

Per-ring P_np / P_pre / P_band (no scatter) for all 8 routes are in
`ring128_summary_rings.tsv`. Every table of every run is in `ring128_summary_runs.json`.

## Result: the model, 8 routes x 16 draws = 128 samples

Each model cell gives the 2.5% / median / 97.5% of the statistic over routes x draws. A star marks
an August value outside that range.

| links | stat | August | model / P_pre | model / P_np |
|---|---|---|---|---|
| 7 | median | 1.176 | 1.076 / 1.285 / 1.469 | 0.889 / 1.022 / 1.116 * |
| 7 | p90 | 1.438 | 1.475 / 1.762 / 2.023 * | 1.085 / 1.239 / 1.383 * |
| 7 | p99 = max | 1.470 | 1.706 / 2.063 / 2.454 * | 1.224 / 1.393 / 1.611 |
| 7 | min | 0.773 | 0.542 / 0.688 / 0.885 | 0.532 / 0.687 / 0.821 |
| 15 | median | 0.987 | 0.942 / 1.090 / 1.217 | 0.853 / 0.987 / 1.078 |
| 15 | p90 | 1.117 | 1.213 / 1.378 / 1.481 * | 1.055 / 1.175 / 1.289 |
| 15 | p99 = max | 1.203 | 1.379 / 1.587 / 1.816 * | 1.167 / 1.314 / 1.515 |
| 31 | median | 0.959 | 0.995 / 1.085 / 1.180 * | 0.903 / 0.987 / 1.070 |
| 31 | p90 | 1.085 | 1.199 / 1.297 / 1.483 * | 1.055 / 1.147 / 1.279 |
| 31 | p99 = max | 1.142 | 1.329 / 1.453 / 1.766 * | 1.150 / 1.246 / 1.456 * |
| 63 | median | 0.969 | 0.990 / 1.075 / 1.149 * | 0.919 / 0.982 / 1.048 |
| 63 | p90 | 1.059 | 1.148 / 1.230 / 1.366 * | 1.024 / 1.110 / 1.192 |
| 63 | p99 = max | 1.134 | 1.238 / 1.370 / 1.664 * | 1.099 / 1.203 / 1.413 |
| all | median | 0.989 | 1.030 / 1.107 / 1.189 * | 0.930 / 0.991 / 1.050 |
| all | p90 | 1.252 | 1.339 / 1.488 / 1.635 * | 1.102 / 1.184 / 1.245 * |
| all | p99 | 1.457 | 1.661 / 1.939 / 2.276 * | 1.246 / 1.354 / 1.523 |
| - | median7 / median63 | 1.214 | 1.031 / 1.196 / 1.393 | 0.923 / 1.029 / 1.155 * |
| - | slower than kfit model | 76 / 128 | 63 / 77 / 87 | 48 / 67 / 79 |
| - | kfit | 0.9616 | 0.987 / 1.060 / 1.134 * | 0.935 / 0.982 / 1.040 |
| - | two-param offset | +988 ps | +605 / +1656 / +2698 | -869 / +263 / +1263 |

**Graded** (`ring128_summary.GRADED`, all 7 must be inside, on the P_pre arm):

* the level, all.median;
* median7 / median63;
* slower;
* p90/median per length.

The model gets 4/7 on P_pre (out: the level and the 7- and 15-link widths) and 6/7 on P_np (out: the
length dependence). **The full stack MISMATCHES** (soft).

The graded set was chosen after a single-route look, and the level was added after the controls (below)
showed that a scale-free set cannot see a wrong column. That much is post hoc. The pass rule (all
inside) is the plainest one available, and no threshold was tuned.

## Controls (8 routes x 8 draws; graded stats inside, of 7)

| config | vs P_pre | vs P_np | what it misses |
|---|---|---|---|
| **model** (band 0.38, region 0.16, wire 0.126) | 4 | 6 | pre: level, 7/15 widths; np: length dependence |
| fast_min (FAST_MIN column) | 4 | 5 | level 0.57-0.63 vs 0.989 |
| slow_max (SLOW_MAX column) | 4 | 5 | level 1.67-1.86 |
| scatter_x2 (0.32 / 0.252) | 3 | 3 | widths too wide everywhere |
| no_region (wire 0.126 only) | 6 | 1 | np: every width and the slow count too narrow |
| no_scatter | 6 | 1 | as no_region |
| nextpnr_scatter (scatter on nextpnr's SDF, no xray) | 6 | 6 | cannot be told from the model on np |
| posthoc_pre (band 0.29, no region; **fitted to this oracle**) | **7** | 0 | - |

Scatter x3 was not run: at sigma_r 0.48 some regions draw negative factors, gen.py clamps those arcs to
0 ps, and rings come out at 0 ps.

So the check can fail, and the wrong columns and the doubled scatter fail it by a wide margin. It can
also pass: posthoc_pre gets 7/7. But that configuration was fitted to this summary, so it shows
only that the criterion is reachable.

## What it shows, and why the 7-link class is different

1. **Against today's nextpnr (P_np), the full stack gets the level, the per-length widths, the
   p99/max and the slow count right, but not the length dependence.** August's 7-link median is
   1.176 against ~0.96-0.99 for longer rings (median7/median63 = 1.214). The model gives 1.03
   (95% range 0.92-1.16). P_band/P_np (no scatter) is flat in length: medians 1.008 / 0.983 / 0.988 /
   0.985 for 7/15/31/63 links. The prjxray delays do not charge a short ring more per link than
   nextpnr does. The region/wire scatter is what makes the widths fit here. That is partly circular,
   because it was sized on this same population's 8.5% median spread (f3_model.md section 3).
2. **Against the emulated pre-patch SDF (P_pre), the length dependence appears: 1.196 (1.03-1.39)
   against 1.214.** It appears for every delay model, including FAST_MIN and SLOW_MAX, so it lives
   in the denominator. The old binary wrote 0/150 ps for in-tile hops (about 295 ps routed) and
   450 + 90|dy| + 45|dx| for cross-tile hops (435-570 ps routed). Over-charging cross-tile hops
   partly cancels the in-tile under-charge on long rings, which have proportionally more multi-tile
   hops: 22% of interconnect arcs at 63 links against 11% at 7, on the default route. Median P_pre/P_np
   over the 8 routes is 0.818 / 0.894 / 0.904 / 0.914 for 7 / 15 / 31 / 63 links. A short ring was
   therefore under-predicted by about 9% more than a long one. At 7 links that is about 0.7 ns per
   loop, the same order as the README's unexplained +988 ps per-loop offset. **If the emulation is
   right, August's "short chains are worse" was largely the old SDF's error, not silicon.** The README
   left that question open ("not settled").
3. **On P_pre the full model is too wide** (7/15-link p90/median, and every p99/max) and too slow by
   about 10% in level. Wire scatter alone or no scatter fits every shape statistic on P_pre (6/7, only
   the level out). Read together: the scatter that F3 sized to the board's 8.5% would then be largely
   double-counting the old SDF's own error. f3_model.md already warned that "the 8.5% includes
   nextpnr's model error ... On the xray SDF the right sigma_r is probably smaller". This result
   points the same way, through the emulation, across routes.

## What it does not show

- **It shows no per-ring agreement.** The comparison is across 8 routes, and none of them is the
  measured route.
- **It does not settle the level.** The P_pre level rests on two inferred emulation details. The
  ro_top cross-check leaves it at about +/-5-10%. band 0.38 was fitted to ro_top long rings, and the
  0.29 that fits here is post hoc.
- **The scatter calibration is not independent.** Region 0.16 was sized on this population's median
  |residual|, so the width match on P_np is partly built in.
- One die, one temperature, as for ring128.

## Grade: soft

The oracle comes from a hard item. But this test sits across routes, against an emulated
denominator, with a scatter calibrated on the same data. The two denominators also give different
answers: P_np says the model is right on width and wrong on length dependence, and P_pre says the
reverse. A hard MISMATCH would claim more than that supports, and so would a hard MATCH. In
`acceptance.py` the item is `ring128_summary` (kind `ring_summary`, soft). It can fail, and the
controls above fail it. It does not gate. ring128 stays the hard test, and it stays BLOCKED until
the August raw data exists.

## Commands

    source ~/dev2/lib/fpgatoolchain/openxc7/export.sh; cd cells
    for s in "" 1 2 3 4 5 6 7; do NEXTPNR_SEED=$s BD_NO_TIGHTEN=1 BD_RLOC=none hw/build_hw.sh ro_many_top
      mkdir -p ../build/fid/ro_many_seeds/${s:-default}
      cp build/hw/ro_many_top/ro_many_top_routed.json build/hw/ro_many_top/ro_many_top.sdf ../build/fid/ro_many_seeds/${s:-default}/; done
    # (NEXTPNR_SEED= empty is the default seed; build_hw.sh treats it as unset)
    python3 gls/fid/ring128_summary.py ../build/fid/ro_many_seeds/* --draws 16 --configs model --tsv rings.tsv --json model.json
    python3 gls/fid/ring128_summary.py ../build/fid/ro_many_seeds/* --draws 8 --configs no_region,no_scatter,scatter_x2,fast_min,slow_max,nextpnr_scatter,posthoc_pre
    GLS_SCATTER_REGION=0.16 GLS_SCATTER=0.126 GLS_SCATTER_MODE=wire \
      python3 gls/fid/acceptance.py --stack full --corner band --items ring128_summary   # MISMATCH (soft), 4/7

xray_delay.py runs on first use (about 70 s and 1.8 GB per route). Each draw is about 1.3 s.
