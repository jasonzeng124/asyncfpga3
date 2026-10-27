import Formal.Cells.CElemCore
import Formal.Cells.ArbCorners

namespace Audit.P3.Misc
open Formal.Cells

/-- InvCh is inhabited (shift channel dU T = dD T = T + 1, dUinf = 2), so
`inv_eternal` is not vacuous. -/
noncomputable def invEx : CElemCore.InvCh where
  dU := fun T => T + 1
  dD := fun T => T + 1
  dUinf := 2
  H_CONT_U := by fun_prop
  H_CONT_D := by fun_prop
  H_MONO_U := fun a b h => by simp only; linarith
  H_MONO_D := fun a b h => by simp only; linarith
  H_INV_UD := fun T => by ring
  H_INV_DU := fun T => by ring
  H_POS_U := by norm_num
  H_POS_D := by norm_num
  H_INF := by norm_num

theorem inv_eternal_inst : ∃ Δ0, invEx.dUinf - invEx.dU 0 < Δ0 ∧ Δ0 < invEx.dUinf ∧ invEx.Osc Δ0 :=
  CElemCore.InvCh.inv_eternal invEx

/-- `guard_universal` needs k ≤ 1: with k = 2, Af = 10, W = -10 the SLOW_MAX
guard `As - Af ≤ As + W` holds and the FAST_MIN margin is -10. -/
theorem guard_needs_k_le_1 : ∃ As Af W Wf kn kd : Int, 0 < kd ∧ 0 ≤ Af ∧ kd * Wf = kn * W ∧
    As - Af ≤ As + W ∧ Af + Wf < 0 := ⟨100, 10, -10, -20, 2, 1, by decide⟩

end Audit.P3.Misc
#print axioms Audit.P3.Misc.inv_eternal_inst
