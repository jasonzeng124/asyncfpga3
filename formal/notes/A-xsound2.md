# A-xsound2: xaudit's timed verdict is sound for continuous-time transport/inertial channels (probe XSound2, shard A)

STATUS: in progress (session 2026-10-29, 07:50 UTC). Checked so far (check.sh, deps in order):
`Formal/Core/XSimChan.lean` + `Formal/Core/XAudit/SoundCells.lean` ([audit] 650 decls, OK).
Written, being checked: `XAudit/SoundChain.lean` (W1), `XAudit/SoundSteps.lean`,
`XSimChanReal.lean`, `XAudit/SoundPhys.lean`, `XSimChanTern.lean`. Nothing below is claimed
until its file is listed as checked.

## The question

`XSim.sound` (and every xaudit verdict built on it, `Design.lean`/`Fast.lean`) is a theorem
about DISCRETE behaviours: time `ℕ`, one step = one `unit_ps`, gates are transport warps on
`ℕ`. The chip is continuous-time, and its LUTs may filter (inertial). Does a verdict printed
by `xaudit` say anything about continuous-time behaviours with transport or inertial gate
channels whose delays lie in the ps bands?

## Answer (what the Lean says)

**Yes for transport, and for inertial gates whose rejection window is at most the abstract
window; no in general for inertial.**

1. **Any time domain, cell semantics** (`Formal/Core/XSimChan.lean`, Mathlib-free).
   Abstract step `k` stands for EVERY instant of time cell `k`, not for one sample. (Sampling
   is the wrong bridge: `TernaryChannels.sample_not_causal`.) Time is any type `τ` with a cell
   map `c : τ → ℕ`. A gate is the zero-delay LUT function `excT` (INIT bit of the pin values at
   the same instant) followed by a channel with the step property `ChanCells c lo hi`: "if the
   excitation is constantly `v` on every instant of cells `[k-hi, k-lo]`, the output is `v` on
   every instant of cell `k`" (`k ≥ 1`).
   - `sound_cells`: every gate `1 ≤ lo` and `ChanCells`, inputs covered cell-wise, power-up
     covered on cell 0 ⇒ `val (c t) w ⊑ x w t` for every instant `t`. Cycles allowed.
   - `sound_of_cells`: `XSim.sound` is the instance `τ = ℕ`, `c = id` (`chanCells_of_winCh`).
   - `dinertial_chanCells`: the discrete inertial channel `delay d ∘ TraceDiscrete.inertial r`
     is `ChanCells id d (d+r)`: covered with the band WIDENED by the rejection width.
   - `InertialCex` (**counterexample**): the same channel with `d = 1`, `r = 2`, whose
     surviving edges are all delayed by exactly 3 (`dinertial_passes`), given its edge-delay
     band `[3,3]`: one buffer, a 1-step input pulse at step 5. `val_8`: the simulator prints
     `1` at step 8; `x_out_zero`: the behaviour is `0` there; `cex_unsound`,
     `cex_not_chanCells`.
2. **Real time** (`Formal/Core/XSimChanReal.lean`, Mathlib). `CellMap q c`: cell `k ≥ 1` in
   `[kq, (k+1)q)`, cell 0 in `(-∞, q)`; `⌊t/q⌋₊` is one (`cellMap_floor`).
   - `Follows Lo Hi x y` (continuous `WinCh`): input constant `v` on `[s-Hi, s-Lo]` ⇒
     `y s = v`. `chan_follows` (transport `[lo,hi]`), `inertialRD_follows` (`InertialRD ρ Δ`
     follows `[Δ, Δ+ρ]`), `boundedInertial_follows` (`[L, H+ρ]`).
   - `chanCells_of_follows`: `Follows Lo Hi` ⇒ `ChanCells c lo hi` when `lo q ≤ Lo` and
     `Hi ≤ hi q` (outward rounding).
   - `boundedInertial_chanCells` (sharper): `BoundedInertial ρ L H` ⇒ `ChanCells c lo hi` when
     `lo q ≤ L`, `H ≤ hi q` and `ρ ≤ (hi+1-lo) q` (rejection window ≤ abstract window).
   - `inertial_wide_not_chanCells` (**the side condition is necessary**): for every `q > 0`,
     `1 ≤ lo ≤ hi`, `ρ > (hi+1-lo) q` there is an input pulse and a
     `BoundedInertial ρ (lo q) (hi q)` output (the filtered pulse) that is not
     `ChanCells ⌊·/q⌋₊ lo hi`. `Cex.cex_real`: one buffer, band `[1,1]`, `q = 1`, `ρ = 3/2`:
     the simulator prints `1`, the inertial behaviour is `0`.
   - `PhysChan q lo hi`: transport in band or bounded inertial in band with `ρ ≤ (hi+1-lo) q`.
     `sound_real`: XSim is sound for ℝ-time networks of such gates.
3. **The executable** (`Formal/Core/XAudit/SoundCells.lean` any `τ`; `SoundPhys.lean` ℝ):
   `valF_sound_*`, `noXF_sound_*`, `noXF_deterministic_*`, `constF_sound_*`, `settled*` read the
   very rows `auditF` computes. In ℝ: with `SatPhys d q x` (every parsed gate = zero-delay INIT
   function then `PhysChan q lo hi`) and inputs covered cell-wise, "no X at `w` on steps
   `[t1,t2]`" means `w` has the printed value at every instant of `[t1 q, (t2+1) q)`, in every
   behaviour; `settledF_phys`: a binary value of a fixed row `T` holds for all `t ≥ T q`.
4. **Rounding** (`Formal/Core/XAudit/SoundSteps.lean`, Mathlib-free): the parser's
   `toSteps` meets `lo·u ≤ L` when `u ≤ L` and always `H ≤ hi·u`; the "raised" flag is set
   iff `L < u`, and then `lo·u > L`: those arcs are NOT covered by the ℝ theorems.
5. **Untimed phase chaining, Wip W1** (`Formal/Core/XAudit/SoundChain.lean`, Mathlib-free):
   `stale_cover_window` (covered-window `sound_postfix` under `Stale D`),
   `stale_settle_window`, `chain_phases`, `chain_noGlitch`, `chain_settles`, with the
   executable's indexing (`prevIn`). Wip/XAudit.lean's statement had an off-by-one indexing
   (its `r (i+1)` is the B row INTO `vs (i+1)` but is claimed to cover phase `i`).
6. **Relation to TernaryChannels** (`Formal/Core/XSimChanTern.lean`): `PhysChan` ⊆
   `NodeChan (lo q) (hi q)` and reads the past by `lo q > 0`; positive lower delay is
   necessary (`zero_delay_chan_unsound`, `zero_delay_inertial_unsound`). `NodeChan` has no
   bound on `ρ` because the untimed analysis does not use windows; the timed one does.

## Findings for the lead

- **A-xaudit.md fidelity table (LUT delay row) is wrong**: "no inertial filtering is
  modelled, which is sound (it only removes behaviours)". Inertial filtering is NOT a subset
  of transport behaviours: an inertial output holds an OLD value after a filtered pulse, which
  no transport channel with the same band can (`InertialCex`, `Cex.cex_real`). xaudit's
  verdicts cover an inertial LUT only if its band is widened (`[L, H + ρ]`) or
  `ρ ≤ (hi+1-lo)·unit`. With Verilog's default inertial (reject = delay, e.g. a 100 ps LUT at
  `unit_ps = 25`) the condition fails; a GLS with inertial LUT paths is then NOT implied clean
  by a clean xaudit run.
- **Raised arcs**: when xaudit prints "NOTE lo < 1 step raised", those arcs are not covered by
  the continuous-time theorems (`SoundSteps.toSteps_raised_lo`).

## Not covered

Involution channels; per-pin skew inside a LUT (all pins sampled at one instant is a
hypothesis); analog effects; inputs that change mid-cell (the stimulus has events on unit
multiples; a concrete input switching off-grid must be X in that cell); phases shorter than
`(n+1)D` in the untimed chain; what `D` is (Stale is a hypothesis).
