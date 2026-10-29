import Formal.Core.XAudit.Events8Arb
import Formal.Core.XAudit.Events9Beh
/-! P11a item 2 (formal fccd12c/141aaee E8Arb, 66200b0 Events9). -/
open Formal.Core.XAudit.Events8Arb
open Formal.Cells (o5B o6B)
open Formal.Cells.ArbBinary (ARB_ST GRANT)

#print axioms Formal.Core.XAudit.Events8Arb.unc_not_harb
#print axioms Formal.Core.XAudit.Events8Arb.noFree_not_harb
#print axioms Formal.Core.XAudit.Events8Arb.ho_pin
#print axioms Formal.Core.XAudit.Events9.design_verdict9
#check @Formal.Core.XAudit.Events9.design_verdict9

namespace P11a
-- own: the INITs in Lean are research bd_arb.v:254,258 (64'hFFF0_FFB2_ACAC_ACAC, 64'h0C0C_0C0C_A0A0_A0A0)
example : ARB_ST = 0xFFF0FFB2ACACACAC := rfl
example : GRANT = 0x0C0C0C0CA0A0A0A0 := rfl
-- own decode of the handover: at t=12 the real R0 (computed in ustate from q) is already high,
-- while g2 (ugrant) is still low; g2 rises at 14.
example : R0h 12 = true ∧ g2h 12 = false ∧ g2h 13 = false ∧ g2h 14 = true := by decide
-- MUTATION: give g2's q pin the same 1-step band as everything else; D1 still bites
-- (real R0 and g2 then rise together at 12; a virtual R0 needs a grant strictly earlier).
def g2m : Formal.Core.TraceDiscrete.Sig := fun t => decide (12 ≤ t)
theorem mut_not_vmerge {loF hiF lo1 hi1 lo2 hi2 : Nat} (h1 : 1 ≤ loF + lo1) (h2 : 1 ≤ loF + lo2) :
    ¬ VMerge loF hiF lo1 hi1 lo2 hi2 lowc g2m R0h := by
  intro hv
  rcases vmerge_needs_grant hv (t := 12) (by decide) with ⟨u, _, hu⟩ | ⟨u, hu1, hu⟩
  · simp [lowc] at hu
  · simp [g2m] at hu; omega
-- MUTATION (negative control): if the real R0 rose 1 step AFTER the grant, VMerge with all
-- bands (1,1)/(0,0) is matched, i.e. the obstruction really is the order R0-before-grant.
theorem ctrl_vmerge : VMerge 1 1 0 0 0 0 lowc g2m (fun t => decide (13 ≤ t)) :=
  ⟨fun t => t - 1, fun t => t, fun t => t, ⟨fun a b h => by omega, fun t => by omega, fun t => by omega⟩,
   ⟨fun a b h => h, fun t => by omega, fun t => by omega⟩, ⟨fun a b h => h, fun t => by omega, fun t => by omega⟩,
   fun t => by by_cases h : 13 ≤ t <;> simp [lowc, g2m, h] <;> (try omega)⟩
#print axioms mut_not_vmerge
#print axioms ctrl_vmerge
end P11a
