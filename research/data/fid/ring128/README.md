# ring128 on its measured route: the hard timing test of the board-fidelity GLS (2026-11-03)

Data: the owner's `research/board/ro_many_aug/` (db3c299b): the August 2026-08-23 ro_many_top build (.bit md5
8ca7e9c6, routed JSON b2199547, nextpnr SDF 07cfac53, nextpnr d216cb36a370f78a) and its per-ring measured periods
(`measured.tsv` 5b0eee1c, 128 rings, 32 each at 7/15/31/63 links, window-to-window spread <= 0.052%).

Checks before comparing:
- md5s equal the owner's README.
- The netlist decoded from the August .bit (fasm2net.py --bit) is EQUIVALENT to the delivered routed JSON
  (fasm_equiv.py, `bits_vs_routed_equiv.txt`): the delays below are on the route the board ran.
- Full-stack delays: xray_delay.py's prjxray RC-tree SDF of that route (md5 f20c1bf4), today's prjxray-db.
  Periods: cells/gls/fid/ring_predict.py (`pred.tsv`) and acceptance.py's own ring walk agree.

## The pre-registered test (acceptance.py run_ring_population, written before the data existed)
`acceptance.py --stack full --items ring128 --ro-many-data research/board/ro_many_aug --corner C`:
median error and every length's median error within +/-5%, and at SLOW_MAX no ring slower than predicted.

| corner | median error | p05 / p95 | by length 7/15/31/63 | verdict |
|---|---|---|---|---|
| SLOW_MAX | +88.2% | +84.4 / +92.5 | 89.6 / 88.7 / 88.3 / 87.5 | MISMATCH on the +/-5% band; 0 rings slower than slow max (the bound holds) |
| FAST_MIN | -35.9% | -37.0 / -34.4 | -36.0 / -35.8 / -35.8 / -35.7 | MISMATCH; every ring slower than fast min (the bound holds) |
| band 0.38 (the model as it was) | **+11.5%** | +9.5 / +13.1 | 11.9 / 11.5 / 11.4 / 11.0 | **MISMATCH** |
| band 0.288 (recalibrated, below) | +0.03% | -1.8 / +1.5 | 0.6 / 0.1 / 0.0 / -0.4 | MATCH (exit 0) |

All 128 measured periods lie between the FAST_MIN and SLOW_MAX predictions.

## The mismatch, and the model fix (research/tools/ring128_fit.py, `fit.txt`)
Per ring, x = (measured - FAST_MIN) / (SLOW_MAX - FAST_MIN): median 0.2877, p05 0.2756, p95 0.3028, range
0.2668-0.3127; by length 0.2833 / 0.2872 / 0.2879 / 0.2911. The band model is one x for the die; 0.38 was fitted to
ro_top's five rings across routes (soft). The hard data put it at 0.288.

0.288 is fitted on this data, so it is judged only on rings it was not fitted to:

| fit on -> predict | fitted x | median error | p05 / p95 | worst ring | pre-registered test |
|---|---|---|---|---|---|
| groups 0-7 -> 8-15 | 0.2879 | +0.04% | -1.88 / +1.52 | 2.93% | PASS |
| groups 8-15 -> 0-7 | 0.2876 | -0.04% | -1.73 / +1.82 | 2.84% | PASS |
| 7,15 links -> 31,63 | 0.2868 | -0.18% | -2.01 / +1.20 | 3.06% | PASS |
| 31,63 links -> 7,15 | 0.2883 | +0.18% | -1.60 / +2.16 | 2.79% | PASS |
| leave one length out (7/15/31/63) | 0.2874-0.2879 | +0.57 / +0.08 / -0.04 / -0.46% | | <= 2.97% | PASS (all four) |

For comparison, the route's own (August, pre-lut-perm-sink) nextpnr SDF with its best global scale: p05/p95
-28.4 / +18.5%, worst 38.6%, 7-link median -15.9%.

## What the residual says about within-die scatter
Residual of the one-x model (model error and die variation together), median |dev| per ring: all 0.76%, 7 links 0.98%,
15 0.58%, 31 0.73%, 63 0.66% (sd 1.08% overall). The GLS's "1x" within-die scatter (region 0.16 + wire 0.126,
f3_model.md section 3) was sized to an 8.5% median ring deviation measured against nextpnr's SDF, and gave 8.33% on
ro_many_top's rings (rebuilt routes): about 11x what this route shows against the prjxray model. f3_model.md's own table puts the measured
0.76% at roughly wire 0.126 alone (0.65%) or region ~0.015. So every "1x / 1.5x / 3x" scatter result in the journal
was run at roughly 11x / 16x / 33x the ring-level variation now measured.

## What this does not show
- Rings exercise LUT and interconnect arcs only. Flip-flops, carry chains, the C-element feedback LUTs and the
  arbiter are not in a ring; x for those cell types is not measured. A soft datum disagrees: gcd's per-iteration
  costs on the August board (another build, other sizes) sat at 0.54-0.72 of [FAST_MIN, SLOW_MAX] on today's gcd_ps
  route (research/data/gcd_ps/cost_model_vs_board.tsv). Not resolved; different builds.
- One die, one day, one operating point (temperature and voltage were not recorded). The corners bracket it.
- The residual is a ring-level (16-128 arcs) number. Variation between two short paths (the bundling margins) is
  only bounded through it; its ratio across lengths (0.98% at 7 links vs 0.66% at 63, vs 2.8x for independent arcs)
  says it is mostly correlated or model error.
- 0.288 is fitted to the data it is tested on; the held-out splits are within one population.
