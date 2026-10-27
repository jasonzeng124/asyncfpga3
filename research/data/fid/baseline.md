# Acceptance baseline: today's GLS (nextpnr SDF, netlist from nextpnr's routed JSON), 2026-10-27

`python3 cells/gls/fid/acceptance.py` with no hooks; nextpnr 9c732bc6303458df, yosys 0.62. Every mismatch is a
row against the model, not a harness bug. Raw reports: build/fid/*.json in the F4 worktree.

## HARD

| item | result | detail |
|---|---|---|
| ring128 | BLOCKED | the measured route's per-ring periods and SDF are not in the repo (README has only ratios against an SDF that no longer exists). Unblock: `RO_OFFLINE=1 RO_MEAS_TSV=... hw/ro_many_measure.py` on the owner's machine, then `--ro-many-data`. Today's rebuild predicts median periods 7268/15406/30846/63099 ps at 7/15/31/63 links (reference only). |
| lutpinmap_gcd (BQ#1 route, fusion on, sdf md5 6f8b99e6 = BOARD-QUEUE #1) | MISMATCH | GLS passes the unpatched bitstream: its netlist is the routed JSON, the FASM is never read. Also measured: on this fusion-on route the 58 corrupted sites are all `lat.odd` latch bits and the corruption changes no vector even when simulated (16/16, identical laps) -- so this route is not a discriminating test for the bug. |
| lutpinmap_gcd_nofuse (BDC_OP_FUSION=0, the August netlist shape) | MISMATCH | same reason; 126 corrupted sites, 9 in each of ucmpi0/1/8/10/11. |
| dsp_constpins (ipow, BD_DSP=1, T9, seed 29) | MISMATCH | GLS passes fast+stalled on the unpatched bitstream (48 FASM lines differ). gen.py models a DSP48E1 from the routed JSON's parameters and refuses INMODE != 0, so the buggy configuration is not even representable. |
| dsp_constpins_inv | MISMATCH | as above (92 lines differ). |
| dsp_areg | NOT RUN | property only: the board showed no functional effect; no repo kernel has an AREG=1 DSP. |

**Harness negative control** (`--netlist-cmd "python3 cells/gls/fid/lut_from_fasm.py"`, a LUT-pin-decoding-only
FASM reader standing in for F2): lutpinmap_gcd_nofuse becomes MATCH -- patched 16/16, unpatched **9/16, vectors
5, 6, 7, 8, 11, 12, 13 never complete, errs=0 on every vector**: absent results, not wrong ones, the board's
signature, and exactly the set BOARD-QUEUE.md #1 records as the August failures. (patches/README.md says "7/16,
nine never completing" for the same event; the two records disagree on the count, so the vector set is soft.)
On the fusion-on BQ#1 route the same reader gives 16/16 for both: the bug is real there but harmless.

## SOFT (across routes: the measured routes are not archived)

ro_top today (one route, default seed) vs the two August routes, predicted/measured - 1:

| links | 7 | 15 | 31 | 63 | 127 |
|---|---|---|---|---|---|
| route A (2026-08-03) | -17.2% | +14.4% | +24.3% | +8.1% | +9.7% |
| route B (2026-08-23) | +6.5% | +15.0% | +2.6% | +2.7% | +9.4% |

Silicon's own route-to-route spread is 0.3% at 127 links and 25% at 7; today's model is +9.5% slow on the 127-link
ring against both measured routes (pessimistic, the safe side), which is the clearest datum here and still only a
cross-route comparison. Every other soft item (bench hang, isprime late read, kernel ns/iteration, gcd latency,
shmoo, mem DCO, sweep stale result, abs negative) is NOT RUN: no archived route, or no GLS rig for it -- see
inventory.md for each reason.

## What this does not show
- Nothing about where in the prjxray band this board sits: no prjxray SDF yet (F1).
- The bitstream items test the MECHANISM on rebuilt routes, not the August bitstreams (none archived).
- The lut_from_fasm double reads LUT pins only; it is not F2 and proves only that the harness can report a match.
