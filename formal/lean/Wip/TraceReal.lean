import Formal.Core.Trace.Real
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Trace benchmark (a): discharge of `RealComplete` -- staging file

NOT CHECKED: needs `Mathlib.Algebra.Order.Archimedean.Real.Basic` (requested).
Once built, move these into `Formal/Core/Trace/Real.lean`.
-/

namespace Formal.Core.TraceReal

theorem realComplete : RealComplete := fun _ hne hbdd => Real.exists_isGLB hne hbdd

theorem inertial_short' {δ a w : ℝ} {y : Sig} (hδ : 0 ≤ δ) (hw : w ≤ δ) (hy : WF y)
    (h : Inertial δ (pulse a w) y) : ∀ t, y t = false :=
  inertial_short realComplete hδ hw hy h

theorem inertial_long' {δ a w : ℝ} {y : Sig} (hδ : 0 ≤ δ) (hw : δ < w) (hy : WF y)
    (h : Inertial δ (pulse a w) y) : y = pulse (a + δ) w :=
  inertial_long realComplete hδ hw hy h

end Formal.Core.TraceReal
