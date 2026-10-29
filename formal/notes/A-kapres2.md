# A-kapres2 (shard A) -- STATUS: IN PROGRESS (session 2026-10-29, probe KapRes2)

Plan (this session):
1. `Formal/Core/Delay/CornerCell.lean`: prove `cell_band` (A-kapres §2 cell-cover lemma).
   Recovering the 2026-10-28 WIP (`Wip/_snapA/Formal/Core/Delay/CornerCell.lean`, Mathlib);
   also a Mathlib-free ℚ core (core `Rat`) so the lemma can be checked before Mathlib is built.
2. `Formal/Core/XAudit/BandCheck.lean`: band-file check rejecting lo > hi (and dropped entries),
   with proved spec (recovering `Wip/_snapA/Formal/Core/XAudit/BandCheck.lean`).
3. κ sweep κ ∈ {0, .02, .04, .06, .08, .10, .12} with xevents8 (Events8), tools under
   `formal/tools-A/kappa/kapres2/`.
4. Rewrite this file with results.

Previous session's substance kept: the committed FAST band files have lo > hi on 2-20 arcs per
seed (prjxray-db BRKH_INT pips with FAST_MIN > FAST_MAX); `Parse.toSteps` reads them as [lo, lo].

## Progress (2026-10-29)
- BandCheck.lean: `readBands` (rejecting reader) + spec written; compiles clean against the
  private overlay (lean -DautoImplicit=false). `Wip/KapRes2/BandCheckRun.lean` (readBands on files):
  seed d slow and indep files OK, committed fast file REJECTED (20 inverted arcs) as expected.
- Overlay of the committed xevents8 chain built (tools-A/kappa/kapres2/mk.sh). Sanity: cell [1,1],
  κ = 0 on seed d reproduces the committed `xaudit/events8/xe8_d_slow.txt` byte for byte.
- BRKH-corrected fast bands: 22/7/8/2 arcs (d/3/4/5); none of them is in the control skeleton
  (check_bands.py brkh --skel), so the fix cannot change any xevents8 verdict.
- Sweep running (κ 0.12 … 0, init 8 cells, finest 1/32).
