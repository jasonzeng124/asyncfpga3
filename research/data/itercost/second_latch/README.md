# A second latch where the cycle waits on a handshake (PROGRAM.md NEXT, owner 2026-11-09)

A measurement. No default changes. Extra stages come from bdc's existing per-site option `BDC_LINK_DEPTHS`.

## Setup

- **Build.** xorshift x0.5 sizes (`xorshift_sizes_T3s50_bench.vh`), bench top, nextpnr `9c732bc6303458df`.
- **Stack and bands.** Same as `../README.md`: the decoded netlist from the bits, prjxray SDF, `fid`, and the calibrated bands with no scatter. One 256-round vector, run twice.
- **Variants:**
  - all3: `ulink_n_trueResult_8=2,ulink_n11__1=2,ulink_n_trueResult_12=4`.
  - p8, p11, p12: one point each.
- **Inner-stage delays.** A new inner stage gets bdc's default SDELAY of 3. The x0.5 sizes give 1 to their own inner stages, so the added stages cost slightly more forward latency than a sized build would.
- **Checks.** Every run returns `cd3132bf`. Every run is EQUIVALENT or carries only the benign mismatch: a `$PACKER_GND` buffer LUT (INIT ..10) on an F7 data input, checked for base_3 and p8_2. Every run has 508 of 510 iterations closed, exact, and summing to the period.

## Premise, checked on the base cycle

The x0.5 seed-1 cycle changes polarity at exactly the three named places. Each is crossed twice per iteration.

`ulink_n_trueResult_8` and `ulink_n11__1` are single `bd_link` stages. `ulink_n_trueResult_12` is already a 3-stage `bd_pipe` (ring floor 3).

## Prediction (journal, committed before running)

| case | predicted period | where the cycle flips |
|---|---|---|
| the coupling is the cause | about 25-30 ns | — |
| expected | 3-8 ns drop | still at umux1 |

## Result (`periods.tsv`)

Period in ns, by NEXTPNR_SEED. Each variant is its own route, so pairs are by seed.

| seed | base | p8 (umux1 point) | all3 | p11 | p12 |
|---:|---:|---:|---:|---:|---:|
| 1 | 39.06 | 34.12 (-4.94) | 35.57 (-3.49) | 39.87 (+0.81) | 44.33 (+5.27) |
| 2 | 38.88 | 33.32 (-5.56) | 34.31 (-4.57) | | |
| 3 | 40.59 | 33.67 (-6.92) | 34.20 (-6.39) | | |
| 4 | 39.43 | 34.55 (-4.88) | 34.65 (-4.78) | | |
| mean | 39.49 | **33.92 (-5.58, 1.164x)** | 34.68 (-4.81, 1.139x) | | |

Base seed 1 is the itercost route, built from the older tree. Bases for seeds 2-4 were rebuilt from the current tree. Their bits differ from the routes in `research/data/xorshift_bench` (`5b3e4d49`, `aadf3cd1`, `e4a6618f`), so a rebuild with the same seed did not reproduce those routes. The variants are paired with the rebuilt bases.

- **Which coupling binds:** umux1's (`ulink_n_trueResult_8`). Adding that one stage gives the whole gain; all three together give a little less.
- **p11** does not move the cycle (+0.8 ns, seed 1 only).
- **p12** keeps the same cycle and lengthens it (+5.3 ns, seed 1 only). The fourth stage sits on the cycle as extra forward latency.

## The new critical cycle (p8 and all3, all 8 routes)

The cycle moves from umux1's select ring to the loop counter ring:

umux0 -> ulink_n7 -> uaddi0 (i+1) -> ulink_n30__1 -> ucmpi1 -> ufork9 / steer -> ucontrol_merge0 -> ulink_n12__0 -> umux0

It still changes polarity twice per iteration, at **ucontrol_merge0 ack -> ulink_n_trueResult_12 req**. So RTZ is still 39-43% of the period (13.2-15.4 ns), against 43-46% for base. The RTZ tail does not fade.

On seed 1, logic rises from 1.0 to 5.0-5.2 ns, because the counter's i+1 is real logic on this ring.

## Reading

- Against the prediction: the size of the drop (5.6 ns mean) is inside the predicted 3-8 ns. The place is wrong: the remaining coupling is at the arbitrated merge, not at umux1.
- A fourth latch in front of the merge does not remove that coupling (all3 includes it).
- The arbiter merge's output request is its granted input's request. It cannot return to zero before that input does, which needs the merge's own acknowledge first. So this coupling is in the merge, not in the latch count beside it.
- Testing that needs storage on the merge's OUTPUT side, between `ucontrol_merge0` and `ucontrol_merge0_f`. That channel has no link and is not a `BDC_LINK_DEPTHS` site, so it needs a bdc change. It has not been run.

## The merge-output test (`BDC_MERGE_OUT_LINK=ucontrol_merge0`)

Added after the result above. bdc/emit.py now has a measurement option: one `bd_link` between the arbitrated merge and its result/index fork. It is empty by default, and the default output is byte-identical. simcheck passes with it.

Variants:
- **mo**: that link alone.
- **p8mo**: that link plus `ulink_n_trueResult_8=2`.

Same setup and seeds 1-4. Every run returns `cd3132bf`. Every run decodes EQUIVALENT except mo_2, which is DRIVER DIFFERS: checked, the benign GND-buffer F7 data-input kind. All iterations are exact.

| seed | base | p8 | mo | p8mo |
|---:|---:|---:|---:|---:|
| 1 | 39.06 | 34.12 | 37.83 | 31.17 |
| 2 | 38.88 | 33.32 | 36.29 | 32.21 |
| 3 | 40.59 | 33.67 | 38.69 | 32.37 |
| 4 | 39.43 | 34.55 | 39.51 | 31.37 |
| mean | 39.49 | 33.91 (-5.58) | 38.08 (-1.41) | **31.78 (-7.71, 1.243x; -6.7..-8.2)** |

- With both latches, the arbiter `ucontrol_merge0` itself leaves the cycle. The loop-counter ring now changes polarity at **ucontrol_merge0_f ack -> ucontrol_merge0_olink**: the fork right after the new latch.
- RTZ is still 40-43% (12.4-14.1 ns).
- So the coupling is not the arbiter's alone. It moves one cell along each time a synchronising cell (mux, merge, fork) is decoupled from the single latch beside it.
- That is consistent with the owner's reading: a lone 4-phase latch next to a synchronising cell couples its return-to-zero into the cycle. But this latch-count fix drains it one site at a time, at 1.4-5.6 ns a site. The RTZ share does not fall.



- 4 routes per variant (p11 and p12 1 route), simulation not silicon, calibrated bands only.
- The full gate (corners plus the combined worst case, at least 8 routes).
- Collatz: per the lead, only if the change helps. It helps xorshift (1.16x, 1.24x with the merge-output link), so collatz is next.
- The sized version: the new links carry bdc's default delays (SDELAY 3, OLINK 4/6); corner_audit would size them.
