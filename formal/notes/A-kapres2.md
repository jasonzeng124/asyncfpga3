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
