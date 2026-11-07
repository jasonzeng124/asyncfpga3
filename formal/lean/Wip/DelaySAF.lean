import Mathlib.Data.Real.Basic
import Formal.Core.Delay.Pure
import Formal.Core.Delay.SAF

/-!
# WIP (NOT PROVED, never built into Formal/): SAF extensions

Everything proved lives in `Formal/Core/Delay/SAF.lean`. The statements here
carry `sorry` and are open.

W1. Per-event delay (the real GLS: the arc depends on the pin that moved and on
    the new value, rise 56 / fall 124). Expected: `saf_transport` becomes
    `Transport 1 dmax`; the bridge needs spacing by the delay of the *earlier*
    change and FIFO order of fires (fires can cross when a rise arc is shorter
    than a fall arc: then the GLS reorders, which no FIFO transport channel does).
W2. Real time. `x` piecewise constant, right-continuous, finitely many change
    times `cs`; a fire at `c + d` copies the left limit of `x` there. Expected:
    contained in `DelayPure.Chan 0 d`, not in `Chan lo hi` for `0 < lo`,
    `hi < 2d`.
W3. n-LUT chains and DAGs: `chain_settle_le_delay` by induction for unary chains;
    `net_eq_delay_of_faithful` for any DAG in topological order.
-/

namespace Formal.Core.DelaySAF.Wip

open Formal.Core.TraceDiscrete

/-- W1: SAF with a delay that depends on the new function value (rise/fall
arcs). An update scheduled by a change entering step `u` fires at
`u + dly (x u)`. Fires are not FIFO when `dly true ≠ dly false`. -/
def fireAt (dly : Bool → Nat) (x : Sig) (t : Nat) : Prop :=
  ∃ k, x (k + 1) ≠ x k ∧ k + 1 + dly (x (k + 1)) = t + 1

/-- W1 relational form: the output changes only at fire steps, copying `x t`. -/
def SafRF (dly : Bool → Nat) (x y : Sig) : Prop :=
  y 0 = x 0 ∧ ∀ t, (fireAt dly x t → y (t + 1) = x t) ∧ (¬ fireAt dly x t → y (t + 1) = y t)

theorem safRF_transport (dly : Bool → Nat) (x y : Sig) (h1 : 1 ≤ dly true)
    (h2 : 1 ≤ dly false) (h : SafRF dly x y) :
    Transport 1 (max (dly true) (dly false)) x y := by
  sorry

/-- W2: real-time SAF, `x` with change times `cs` (right-continuous). -/
def SafR (d : ℝ) (x : ℝ → Bool) (cs : List ℝ) (y : ℝ → Bool) : Prop :=
  ∀ t, ((∀ c ∈ cs, t < c + d) → y t = x (t - d)) ∧
    ∀ c ∈ cs, c + d ≤ t → (∀ c' ∈ cs, c' + d ≤ t → c' ≤ c) →
      ∃ η > 0, ∀ u, c + d - η < u → u < c + d → y t = x u

theorem safR_chan (d : ℝ) (hd : 0 < d) (x y : ℝ → Bool) (cs : List ℝ)
    (hx : ∀ a b, a ≤ b → (∀ c ∈ cs, ¬ (a < c ∧ c ≤ b)) → x a = x b)
    (h : SafR d x cs y) : Formal.Core.DelayPure.Chan 0 d x y := by
  sorry

end Formal.Core.DelaySAF.Wip
