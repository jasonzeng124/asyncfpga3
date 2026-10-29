# A-kapres2 (shard A, probe KapRes2, session 2026-10-29)

STATUS: done for Lean (CornerCell, BandCheck checked) and for the κ sweep on the E8Mux bands at
coarse resolution (cells of 1/4, five point corners per κ; κ = 0 refined to 1/16, see §3.3).
Residual-at-cell items that pass at every point corner are NOT resolved (cell-width artefacts or
real failures between the point corners; §3.4). Old-band sweep stopped after κ = 0.12 (comparison).

Summary of the sweep (xevents8 = committed `Events8Main`, E8Mux corrected bands, corner model
`[(1-κ)·min lerp, (1+κ)·max lerp]` cell bands, κ ∈ {0.12, 0.10, …, 0}):
- **Fails at point corners** (a real corner where the checker cannot discharge the item; not a
  counterexample, the checker is conservative):
  - seed d: Guard ENTRY `ucontrol_merge2.uarb1.ua2` pin0 and `ucontrol_merge3.uarb1.ua2` pin0 at
    κ = 0.12 and 0.10 (every point corner at 0.12; −7..−15 and −8..−48 ps at 0.10);
    `ucontrol_merge3.uarb1.ua1` pin0 at κ = 0.12 (all corners) and 0.10 (c = 0 only, −18).
    At κ ≤ 0.08 all three pass at every point corner run.
  - seed 3: Line `arb:ucontrol_merge12.uarb2.ugrant` at κ = 0.12, c = 1 only (margin 0, strict).
  - seed 5: Back `urig.uenv1.u` pin1 (rig environment, as in A-kapres) at κ = 0.12 (all corners,
    −25..−95), 0.10 (all, −5..−48), 0.08 (c = 1, −2). At κ ≤ 0.06 it passes at every point run.
  - seed 4: none.
- **No item fails at any point corner run at κ ≤ 0.06**, on any seed.
- **Discharged on the whole corner interval [0,1]** (a cover by cells, CornerCell.cover_mem +
  cell_band_nat): seed 4 at κ ≤ 0.06 (after refining to 1/8). For d, 3, 5 see §3.3.
- No structural residual item anywhere (xevents8 has none left on gcd_hw; HDsub, H_ARB, SelOK,
  SelPart, SatPin stay hypotheses of `design_verdict8`).

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


## 3. κ sweep with xevents8

### 3.1 Pipeline (`formal/tools-A/kappa/kapres2/`)
Per seed and cell `[ca,cb]`, κ descending: `cornerband2.py` (cell band = CornerCell `cellLo`/`cellHi`,
exact ℚ, outward rounding; inputs validated, lo > hi REJECTED) -> `events4/skel.py` ->
`check_bands.check` on both files -> `events8/cert8.py` (untrusted) -> committed `Events8Main`
(`lean --run` on a private olean overlay of the committed chain, `mk.sh`). A run is accepted only
with `Design.WF true`, `Recog6 node failures 0`, `Net4.OK7 true`, log `accepted by runLog: true` and
`501 nodes (36 virtual, H_ARB)`. Refinement rule and `implied_clean` reuse as A-kapres §2 (a
cell inside a CLEAN cell of a larger-or-equal κ is not re-run: CornerCell.cellLo_anti/cellHi_mono).
- **Arbiter core pinned.** At 09:33 `events4/model.py` (commit 591cd51) switched its default to
  the E8ArbFix "fix" virtual arbiter core (519 nodes, 54 virtual), made for Events9Arb, not for
  Events8's HARB7. Every run here uses the Events8 core: kapres2.py forces `XA_ARB=old` and runs a
  snapshot of the committed events4/6/7/8 python (`$KR/xa`, from 591cd51). Checked: on the seed-d
  slow skeleton, 591cd51 + `XA_ARB=old` gives a byte-identical certificate to 591cd51^ (the tools
  every committed xevents8 result used); the "fix" default does not. All 116 old-band and all
  E8Mux-band outputs print `501 nodes (36 virtual` (no run used the fix core).
- **Bands.** E8Mux NEW bands (`tools-A/xaudit/e8mux/`, scratch `e8mux/w/<s>/new/`: slice OUTMUX hop on
  O5/MUXF/CARRY4/x5FF exits; lo > hi rows hulled by routed2x `--inverted hull`), plus
  `check_bands.py fix` (BRKH_INT fast hull, 14/3/6/2 arcs d/3/4/5). No BRKH arc is in the control
  skeleton (same netlists), so neither treatment changes a verdict.
- **Sanity.** Cell `[1,1]` at κ = 0 gives exactly the slow band file (all 4 seeds, old and new
  bands); on the old seed-d bands the xevents8 output is byte-identical to the committed
  `xaudit/events8/xe8_d_slow.txt`.
- **Lean band check.** `Wip/KapRes2/BandCheckRun.lean` (`BandCheck.readBands`) on all 221 band files
  the sweep used (every skeleton band file fed to xevents8, the corrected fast and the slow
  inputs): `221 files, 0 rejected` (`kapres2/bandcheck_run.txt`). On the committed (uncorrected)
  seed-d fast file it rejects (negative control on real data).

### 3.2 Results, E8Mux bands (`runs_e8/`, `table2_e8.txt`; depth-0 sweep: 4 cells of 1/4, end corners)
Per item: largest κ in {0.12 … 0} at which it is absent from every cell of the cover ("best"),
and where it FAILS at a point corner. Margins ps, strict. Prefix `urig.udut.` dropped.

| seed | item | best κ (1/4 cells) | fails at point corners |
|---|---|---|---|
| d | Guard `ucontrol_merge2.uarb1.ua2` pin0 | none (cells to κ=0) | κ .12: all 5 (−57..−123); κ .10: all 5 (−7..−15) |
| d | Guard `ucontrol_merge3.uarb1.ua2` pin0 | none | κ .12: all 5 (−114..−130); κ .10: c=0..3/4 (−48..−8) |
| d | Guard `ucontrol_merge3.uarb1.ua1` pin0 | none | κ .12: all 5 (−85..−29); κ .10: c=0 (−18) |
| d | Guard `merge11.uarb1.ua1` p0 / `merge2.uarb1.ua1` p0 / `merge9.uarb1.ua1` p0 / `merge11.uarb1.ua2` p1 | .02 / .04 / .04 / .08 | none |
| d | Line `arb:ucontrol_merge12.uarb2.ugrant` | .06 | none |
| 3 | Guard `ucontrol_merge9.uarb1.ua2` pin1 | none (cells to κ=0, −4 at 0) | none |
| 3 | Line `arb:ucontrol_merge12.uarb2.ugrant` | 0 | κ .12: c=1 (0) |
| 3 | Line `arb:merge4.uarb1.ugrant`; Guards merge10.ua1, merge11.ua2, merge6.ua2 | .04 | none |
| 3 | Guards merge12.uarb1.ua2, merge4.ua1 / merge10.ua2, merge12.uarb2.ua2, merge3.ua1 / Back `ulink_n_falseResult_77` p1 | .06 / .08 / .10 | none |
| 4 | Guard `ucontrol_merge3.uarb1.ua2` pin0 | 0 (refined: .06) | none |
| 4 | Guard `merge3.uarb1.ua1` p1 / Line `arb:merge12` grant | .10 / .08 | none |
| 5 | Back `urig.uenv1.u` pin1 (rig env) | none (cells to κ=0) | κ .12: all 5 (−25..−95); κ .10: all 5 (−5..−48); κ .08: c=1 (−2) |
| 5 | Line `arb:merge12` grant / Back `ulink_n_trueResult_28` s0 p1, Guards merge2.ua1, merge4.ua2 / Guard merge3.ua1 | .02 / .06 / .08 | none |

"none (cells to κ=0)" at 1/4 resolution only: see 3.3.

### 3.3 Refinement (cells to 1/8 and 1/16)
- **κ = 0, seeds d, 3, 5** (`summary_k0refine.json`): every item disappears; covers d 6 cells,
  3 5 cells, 5 7 cells (widths 1/8 and 1/4), contiguous [0,1], 0 cells with residual items. With
  seed 4 (clean at 1/4): **at κ = 0 every gcd_hw seed is discharged on the whole corner
  interval** (no residual item of `design_verdict8` on any cell).
- **κ = 0.06, seed 4** (`summary_refine.json`): 7 cells (1/8, one 1/4), all clean -> seed 4 is
  discharged on [0,1] for every κ ≤ 0.06.
