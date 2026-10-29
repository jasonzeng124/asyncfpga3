import Formal.Cells.ResetCapstoneMap
import Formal.Cells.ResetWitness2
/-! P10c items 1-2: ResetCapstone* (260e219), ResetCapstoneMap, ResetWitness2 (1d2124d). -/
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.ResetContract Formal.Cells.ResetGcd

#print axioms Formal.Cells.ResetCapstone.gcd_hw_safe_after_reset
#print axioms Formal.Cells.ResetCapstone.gcd_hw_safe_from_reset
#print axioms Formal.Cells.ResetCapstone.glue_cells
#print axioms Formal.Cells.ResetCapstone.rtl_not_idle
#print axioms Formal.Cells.ResetCapstone.atS_of_rtl
#print axioms Formal.Cells.ResetCapstone.cap_idle0
#print axioms Formal.Cells.ResetCapstone.reset_capstone_nonvac
#print axioms Formal.Cells.ResetCapstone.gcd_hw_safe_from_reset_nonvac
#print axioms Formal.Cells.ResetCapstoneMap.gcd_hw_safe_after_reset_map
#print axioms Formal.Cells.ResetCapstoneMap.μT_wire
#print axioms Formal.Cells.ResetCapstoneMap.μW_not_wire
#print axioms Formal.Cells.ResetCapstoneMap.reset_capstone_map_nonvac
#print axioms Formal.Cells.ResetWitness2.reset_capstone_nonvac2
#print axioms Formal.Cells.ResetWitness2.nondegenerate
#print axioms Formal.Cells.ResetWitness2.wBounded
#print axioms Formal.Cells.ResetWitness2.nonvac_net3
#print axioms Formal.Cells.ResetWitness2.link_moves
#print axioms Formal.Cells.ResetWitness2.delays_vary

namespace P10c
open Formal.Cells.ResetCapstone

/-- The glue's prefix does not depend on `r` at all: ticks 0..2 are virtual. -/
example (r : Fin NC → Chan) (T0 : Nat) : (gl r T0 ⟨0, by decide⟩).req 1 = true ∧
    (gl r T0 ⟨3, by decide⟩).req 1 = false ∧ (gl r T0 ⟨3, by decide⟩).req 2 = true ∧
    (gl r T0 ⟨3, by decide⟩).ack 2 = false := by
  simp [gl, preR]

/-- Item 2: re-feed ResetWitness2's joint witness INTO the headline itself (D = 2, W = 1). -/
example : ∀ e, T0of 2 1 ≤ e → fallB (frzC Wit.chW out0).ack e = true →
    (frzC Wit.chW out0).dat e = Nat.gcd 12 18 := by
  obtain ⟨v, Rn, D, W, E, r, μ, hD, hW, hB, hR, hH, hM, hT, hC, hBd, hS⟩ :=
    Formal.Cells.ResetWitness2.reset_capstone_nonvac2
  -- the existential hides D,W; instead apply with the concrete terms
  exact gcd_hw_safe_after_reset 12 18 (by decide) (by decide) Formal.Cells.ResetWitness2.wRun
    Formal.Cells.ResetWitness2.wBounded Formal.Cells.ResetWitness2.F
    Formal.Cells.ResetWitness2.w_rst_clean (by decide) (frzC Wit.chW) μW μW_ok
    (by
      intro c
      obtain ⟨a1, _, a3, _, _, _, a7, a8⟩ := μW_facts c
      refine ⟨?_, ?_⟩
      · rw [Formal.Cells.ResetWitness2.w_reset _ a1 _ (by decide) (by decide), a7]; rfl
      · rw [Formal.Cells.ResetWitness2.w_reset _ a3 _ (by decide) (by decide), a8]; rfl)
    (fun o => frozen_cellA _ _ _ _ (side_all o) (Wit.w_cells o))
    (fun c t _ _ _ => rfl) (fun t _ => by unfold riseB; cases hot start <;> rfl)

/-- Vacuity of the joint witness's conclusion: the frozen out0 ack never falls. -/
example : ∀ e, fallB (frzC Wit.chW out0).ack e = false := by
  intro e; simp [fallB, frzC]

/-- Mutation (H_MAP): reading channel 3's acknowledge from a cold node breaks MapOK. -/
def μbad : ChanMap := ⟨μW.μR, fun _ => 65⟩
example : ¬ MapOK μbad := by
  intro h
  have := (h ⟨3, by decide⟩).2.2.2.2.2
  have h65 : (65 : Nat) ∉ onesL := by decide
  exact h65 (this.2 rfl)

/-- Mutation (ResetWitness2 delays): node 69 does NOT follow after 2 steps at 101. -/
example : Formal.Cells.ResetWitness2.respChk 69 101 2 true = false := by decide +kernel
/-- Mutation: node 74 does not follow after 2 (its delay really is 3). -/
example : Formal.Cells.ResetWitness2.respChk 74 109 2 true = false := by decide +kernel
/-- D, W really are 2, 1 in the Bounded instance fed to the headline. -/
example : Bounded gNet Formal.Cells.ResetWitness2.wv Formal.Cells.ResetWitness2.wRun 2 1 :=
  Formal.Cells.ResetWitness2.wBounded
/-- T0 = 92 and rst held to 93: H_HOLD_LONG' would fail with rst released at 91. -/
example : ¬ (T0of 2 1 ≤ 91) := by decide
end P10c
