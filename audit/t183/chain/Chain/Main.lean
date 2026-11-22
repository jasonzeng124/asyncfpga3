import Chain.E2
import Chain.FO
import Chain.Build
import Formal.Rewrite.RingFuse.AutoCollatzRF
/-! Audit T183: does the A24 (eq2) + fuse_check + A26 chain compose into ONE theorem about the item-42 build graph? -/
namespace Chain
open Formal.Net.Kahn Formal.Net.GcdHw
open Formal.Net.AutoCollatzRF (kC St)
open Formal.Net.CollatzRFHw (T0 T1)

-- link objects: literal equalities between the separately generated rule lists
theorem build_eq_e2out : ChainBuild.rules = ChainE2.rulesOut := by decide
theorem e2in_eq_foin : ChainE2.rulesIn = ChainFO.rulesIn := by decide
theorem foout_eq_a26 : ChainFO.rulesOut = Formal.Net.CollatzRFHw.rules := by decide

theorem init_ok (n₀ : Nat) : ∀ ch, 2 ≤ ch → St T0 [n₀] ch = [] := by
  intro ch h
  simp only [St, ofL_lmap]
  by_cases hc : ch < 50
  · have : ∀ c, c < 50 → 2 ≤ c → ofL T0 c = [] := by decide
    rw [this ch hc h]; rfl
  · have hl : (T0).length = 50 := by decide
    have : ofL T0 ch = [] := by
      simp only [ofL]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hl]; omega)]; rfl
    rw [this]; rfl

theorem out_val (r : Nat) : St T1 [r] 48 = [r] := by
  simp only [St, ofL_lmap]; rfl

/-- The composed statement for the item-42 build graph (bdc's plan under the build knobs, as dfimport reads it):
on every input where the C (kC) returns r, (1) some complete run ends with [r] on the output channel and
(2) every complete run ends with [r] on the output channel. -/
theorem build_computes {fuel n₀ r : Nat} (h : kC fuel n₀ = some r) :
    (∃ m t, Run (step (graph ChainBuild.rules)) (St T0 [n₀]) m t ∧ Terminal (step (graph ChainBuild.rules)) t ∧
        t ChainBuild.chOut = [r]) ∧
    (∀ m t, Run (step (graph ChainBuild.rules)) (St T0 [n₀]) m t → Terminal (step (graph ChainBuild.rules)) t →
        t ChainBuild.chOut = [r]) := by
  have A := Formal.Net.AutoCollatzRF.auto_computes h
  have hc : ChainBuild.chOut = 46 := rfl
  rw [hc, build_eq_e2out]
  constructor
  · obtain ⟨n, hn⟩ := A.1
    have term : Terminal (step (graph Formal.Net.CollatzRFHw.rules)) (St T1 [r]) :=
      Formal.Net.AutoCollatzRF.final_terminal r
    have hn' : Run (step (graph Formal.Net.CollatzRFHw.rules)) (St T0 [n₀]) n (St T1 [r]) := hn
    rw [← foout_eq_a26] at hn' term
    obtain ⟨t1, m1, r1, T1', k1⟩ := ChainFO.pass_backward (init_ok n₀) hn' term
    rw [← e2in_eq_foin] at r1 T1'
    obtain ⟨t2, m2, r2, T2, k2⟩ := ChainE2.pass_forward (init_ok n₀) r1 T1'
    refine ⟨m2, t2, r2, T2, ?_⟩
    rw [k2.2, k1.2, out_val]
  · intro m t hr ht
    obtain ⟨t1, m1, r1, T1', k1⟩ := ChainE2.pass_backward (init_ok n₀) hr ht
    rw [e2in_eq_foin] at r1 T1'
    obtain ⟨t2, m2, r2, T2, k2⟩ := ChainFO.pass_forward (init_ok n₀) r1 T1'
    rw [foout_eq_a26] at r2 T2
    have := A.2.1 m2 t2 r2 T2
    rw [← k1.2, ← k2.2, this, out_val]
end Chain
#print axioms Chain.build_computes
