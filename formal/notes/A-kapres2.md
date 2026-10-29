# A-kapres2 (shard A, probe KapRes2, session 2026-10-29)

STATUS: PARTIAL -- Lean done (CornerCell, BandCheck checked); κ sweep with xevents8 RUNNING
(results below are filled in as seeds finish; see "Sweep").

## 1. `Formal/Core/Delay/CornerCell.lean` (cell_band, Mathlib)

Recovered from the 2026-10-28 WIP (`Wip/_snapA/Formal/Core/Delay/CornerCell.lean`), only the
docstring paths changed. `check.sh Formal/Core/Delay/CornerCell.lean`: `[audit] 1317
declarations checked`, `[check] OK` (with autoImplicit=false).

**Assumed** (explicit hypotheses): an arc's fast endpoint `F ∈ [f0,f1]`, slow endpoint
`S ∈ [s0,s1]` (no `F ≤ S` needed); nominal delay `Corner.lerp F S c` at the shared corner `c`;
`Corner.Scat κ (lerp F S c) d` with `0 ≤ κ ≤ 1`; the corner `c` in the cell `[ca,cb] ⊆ [0,1]`.
**Proved**:
- `cell_band`: A-kapres §2's proposed statement (without its `0 ≤ ca`, `cb ≤ 1`, not needed);
- `cell_band_mem`: such a `d` lies in `[(1-κ)·min(lerp f0 s0 ca, lerp f0 s0 cb), (1+κ)·max(lerp f1 s1 ca, lerp f1 s1 cb)]`;
- `cell_band_int`: the same for the integer band `cellLo` / `cellHi` (ℚ, floor / ceiling): the
  exact transcription of `tools-A/kappa/kapres2/cornerband2.py`;
- `cell_band_nat`, `realizes_cell`: the same for the ℕ model `Substrate.CornerNat` (via
  `Substrate.scat_real`): every arc of an assignment realised at ONE ℕ corner inside the cell is
  in its cell band;
- `corner_mem_iff`: the ℕ corner `w1/(w0+w1)` is in a rational cell iff two ℚ inequalities hold;
- `cellLo_anti`, `cellHi_mono`: widening κ or the cell widens every band (the sweep's
  `implied_clean` reuse);
- `cover_mem`: a list of cells that chains from 0 to 1 (`Chain`) contains every `c ∈ [0,1]`.
**Not covered**: whether the corner model holds of silicon; whether the band files carry
prjxray's numbers; anything about the timing checker (its soundness is Events8's
`design_verdict8`). If a band file has `f0 > f1` the hypothesis `f0 ≤ F ≤ f1` is unsatisfiable
and the theorem says nothing about that arc: that is why the inputs are validated (§2).

Mathlib-free companion: `Wip/KapRes2/CornerCellQ.lean` (core `Rat`, `grind`; 19 decls):
`cell_band`, `cell_band_mem`, `cell_band_int` (Rat.floor/ceil), `cellLo_anti`, `cellHi_mono`,
`cover_mem`, all over ℚ. Checked with `check.sh Wip/KapRes2/CornerCellQ.lean` (OK; the audit there
counts only `Formal.*` modules, so a separate axiom audit was run: 25 declarations, only the
standard axioms). It is in Wip because I own no second Formal path; the lead may promote it.

## 2. `Formal/Core/XAudit/BandCheck.lean` (the band reader rejects lo > hi)

`check.sh Formal/Core/XAudit/Design.lean Formal/Core/XAudit/Parse.lean Formal/Core/XAudit/BandCheck.lean`
(Parse had no olean in .lake/build yet): `[audit] 761 declarations checked`, `[check] OK`.

The trusted reader `Parse.parseBands` / `toSteps` silently DROPS an entry that is not two
naturals (default band) and silently NARROWS `lo > hi` to `[lo, lo]` (`toSteps_inverted`).
**New**: `readBands j := if jsonBandsOK j then .ok (parseBands j) else .error (violations)`.
**Proved**:
- `readBands_ok_iff`: accepted exactly when `jsonBandsOK`, and then the result IS `parseBands j`;
- `readBands_spec`: on acceptance every raw `cells`/`arcs` entry is read with its own band, every
  band read (cells, arcs, lut, route, pad, feedback) has `lo ≤ hi`, and the 1-ps step bands are
  the file's bands exactly (only `lo = 0` -> 1, flagged as before): no band is narrowed;
- `readBands_rejects_entry` / `readBands_rejects_field`: a `cells`/`arcs` entry or a
  `lut`/`route`/`feedback`/`pad_steps` field with `lo > hi`, or not two naturals, gives `.error`;
- `invertedFile_control` (negative control): a file with one arc `[202, 105]` (the BRKH_INT
  shape): `parseBands` keeps it and `toSteps` narrows it to `[202, 202]` unflagged; `readBands`
  rejects it.
**Trusted** as before: `Lean.Json`'s parser. **Not covered**: the numbers' provenance.
**Not wired**: `Events*Main.run` still call `parseBands` (not my files). For the lead: replace
`parseBands (← readJson bandp)` by `← IO.ofExcept (readBands (← readJson bandp))` (one line per
executable). Until then, the sweep runs `Wip/KapRes2/BandCheckRun.lean` (`readBands` on files).
On real data: the committed seed-d fast band file is REJECTED (20 inverted arcs), slow / indep
accepted.

## 3. Sweep (xevents8) -- see below

The BRKH correction (`check_bands.py fix`: fast hull `[FAST_MIN-97k, FAST_MAX+97k]` on the
22/7/8/2 BRKH_INT arcs of seeds d/3/4/5) touches no arc of the control skeleton
(`check_bands.py brkh --skel`), so it cannot change an xevents8 verdict.
Sanity: cell `[1,1]`, κ = 0 on seed d reproduces the committed `xaudit/events8/xe8_d_slow.txt`
byte for byte.
