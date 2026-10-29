# A-xinert: an inertial option for xaudit (probe XInert, shard A)

STATUS: in progress (09:00 UTC). Code written (Parse/Main additive, SoundInertial.lean); checking; runs pending.

## The problem

XSound2 proved that xaudit's timed verdicts hold in continuous time for two kinds of gate:
- transport gates;
- bounded-inertial gates (`DelayInertial.BoundedInertial ρ L H`) whose reject window satisfies
  ρ ≤ (hi+1−lo)·unit (`XSimChanReal.boundedInertial_chanCells`).

The side condition is necessary (`inertial_wide_not_chanCells`). So a run that is clean with
transport bands says nothing about a gate whose reject window is wider. This probe adds:
- a way to state ρ;
- a mode that widens the band to restore the side condition;
- a mode that refuses to run instead;
- the soundness theorem connecting both to the executable.

## What was added

**Band format (optional `inertial` key; absent means all 0):**

    "inertial": 50            -- every LUT output and routed arc, ps
    "inertial": "delay"       -- Verilog/iverilog default: reject = the delay, taken as the band's hi (ps)
    "inertial": {"lut": R, "route": R, "feedback": R, "cells": {"cell": R}, "arcs": {"cell/I3": R}}

The keys are the same as `cells` / `arcs` of the band file. Pads are always transport.

**CLI (additive):**

    --inertial widen|check  [--rho R] [--rho-lut R] [--rho-route R] [--rho-feedback R]   (R = ps | delay)

- **Without `--inertial`:** the old code path runs, and the output is byte-identical (diffed below).
- **`widen`:** every gate with window ρ gets `hi' = max(hi, lo + ⌈ρ/unit⌉ − 1)`. That is the least
  hi' ≥ hi with ρ ≤ (hi'+1−lo)·unit. The run prints how many gates were widened and by how much.
- **`check`:** if any gate would be widened, the run is refused before simulation (exit 4) and
  the offenders are listed. Otherwise it runs the unchanged design.

**Code.**
- `Parse.lean`, additive:
  - `RhoSpec`, `Inert`, `parseInert`;
  - `widenHi`, `widenGate`, `widenD`;
  - `applyInertial`, which reconstructs each gate's ps band and window from the band file
    (TRUSTED). It re-rounds every reconstructed band and throws on any mismatch with the parsed
    step band.
- `Main.lean`: the `--inertial` branch and two header lines, printed only under `--inertial`.

**Inverted bands (lead's extra item, from E8Mux).**
- `Parse.checkedSteps` rejects a ps band with lo > hi ("NOT RECOGNISED" error) instead of letting
  `toSteps` narrow it to [lo, lo].
- `bandFor` now uses it. This is the one non-additive edit, and it changes behaviour only on
  inverted bands.

## Lean: `Formal/Core/XAudit/SoundInertial.lean` (Mathlib, ℝ)

(see the file header for the full list)
- `checkedSteps_ok`: an accepted band has lo ≤ hi and is rounded by `toSteps`.
  `checkedSteps_inverted`: an inverted band is rejected.
- `toSteps_hi_ceil`: for an accepted band, step hi = max 1 ⌈H/u⌉, so there is no narrowing.
- `checkedSteps_inside`: if also u ≤ L, then lo·u ≤ L ≤ H ≤ hi·u and 1 ≤ lo ≤ hi.
- `widenHi_window`: ρ ≤ (widenHi+1−lo)·u. `widenHi_ge`: hi ≤ widenHi.
- `widenHi_eq_of_window`, `widened_wide`: a gate is widened iff (hi+1−lo)·u < ρ, which is exactly
  the case where `inertial_wide_not_chanCells` gives a counterexample for the unwidened band.
  So `check`'s refusals are necessary. `widenHi_eq_of_le_unit`: ρ ≤ unit never widens.
- `widenD_zero`, `widenD_eq_of_window`: with all ρ = 0, or when `check` passes, the simulated
  design is the parsed design.
- `GateOK q lo hi ρ e o`: there is a ps band [L,H] with lo·q ≤ L and H ≤ hi·q (the ORIGINAL step
  band), and the channel is transport in [L,H], or BoundedInertial ρ' L H with ρ' ≤ ρ.
  - `gateOK_of_toSteps`: the parser's rounding gives `GateOK` when the arc is not raised.
  - `gateOK_verilog`: a Verilog-default inertial gate (`Inertial Δ`, Δ ∈ [L,H]) is `GateOK` with
    ρ = H. This is the executable's `"delay"`.
- `physChan_widen`, `satPhys_widenD`: if every gate is `GateOK`, then `SatPhys (widenD …)`.
- `valF_sound_inertial`, `noXF_sound_inertial`, `constF_sound_inertial`, `settledF_inertial`:
  the printed verdicts on the widened design hold at every real instant, in every behaviour.

## Results

(pending)
