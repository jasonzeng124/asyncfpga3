import Formal.Core.Delay.Inertial

/-!
# WIP (not built, not claimed): open items for the inertial-delay probe

Everything below is a STATEMENT ONLY (`sorry`). The proved part is
`Formal/Core/Delay/Inertial.lean`.
-/

namespace Formal.Core.DelayInertial.Wip

open Formal.Core.DelayInertial

/-! ## 1. Faithfulness of `Filt` to the Verilog event-queue rule

A finitely-variable signal as an initial value plus strictly increasing toggle times.
The event-queue rule (IEEE 1364 inertial, reject limit = delay): each input toggle at
`tᵢ` schedules `x(tᵢ)` at `tᵢ + δ`; a toggle at `tᵢ₊₁ < tᵢ + δ` cancels it. -/

structure Toggles where
  init : Bool
  times : List ℝ
  sorted : times.Pairwise (· < ·)

/-- Value at `u`: `init` xor parity of the toggles at or before `u` (right-continuous). -/
noncomputable def Toggles.eval (x : Toggles) (u : ℝ) : Bool :=
  x.init ^^ ((x.times.filter (fun t => decide (t ≤ u))).length % 2 == 1)

/-- Surviving toggles: those followed by at least `δ` of stability. -/
def survivors (δ : ℝ) : List ℝ → List ℝ
  | [] => []
  | [t] => [t]
  | t :: t' :: ts => if t + δ ≤ t' then t :: survivors δ (t' :: ts) else survivors δ (t' :: ts)

/-- Event-queue output (not normalised: consecutive survivors may carry equal values). -/
noncomputable def queueOut (δ : ℝ) (x : Toggles) (s : ℝ) : Bool :=
  match ((survivors δ x.times).filter (fun t => decide (t + δ ≤ s))).getLast? with
  | none => x.init
  | some t => x.eval t

/-- TODO: the semantic filter agrees with the event-queue rule. -/
theorem inertial_eq_queue (δ : ℝ) (hδ : 0 < δ) (x : Toggles) :
    Inertial δ x.eval (queueOut δ x) := by
  sorry

/-- TODO: existence of the filter output for every finitely-variable input
(follows from `inertial_eq_queue`). -/
theorem filt_exists (ρ : ℝ) (hρ : 0 < ρ) (x : Toggles) : ∃ z, Filt ρ x.eval z := by
  sorry

/-! ## 2. Per-transition nondeterministic bounded inertial channel

`BoundedInertial` fixes ONE unknown delay per instance. Silicon delay also varies per
transition (rise/fall, which input switched: the LUT specify block has one path per
input pin, `cells/gls/prims.v`). A per-transition version: every surviving input
change at `t` appears at some `t + dᵢ` with `dᵢ ∈ [lo, hi]`, order preserved. Statement of
the expected pulse property only. -/

/-- TODO: define `BoundedInertialPT` and prove: a pulse of width `w ≥ ρ` produces an
output pulse of width in `[w - (hi - lo), w + (hi - lo)]` (and none if `w < ρ`). -/
theorem boundedInertialPT_pulse_width : True := by
  trivial

/-! ## 3. Asymmetric rise/fall (iverilog `(A => O) = (tr, tf)`)

With distinct rise/fall delays a 0→1→0 input pulse of width `w` would, if it survives,
give an output pulse of width `w + tf - tr`; which pulses survive (reject limit taken from
which edge's delay, and iverilog's exact cancellation rule) is UNVERIFIED: check against
IEEE 1364-2005 §14.6 and a two-LUT iverilog probe before modelling. Not in the Formal file. -/

theorem asymmetric_inertial_todo : True := by
  trivial

end Formal.Core.DelayInertial.Wip
