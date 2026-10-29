import Formal.Cells.ResetGcdVec2
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.ResetContract Formal.Cells.ResetGcd Formal.Cells.ResetGcdVec Formal.Cells.ResetGcdVec2
/-! P8 item 6: the network-derived reset theorem is applied to the concrete witness run,
with NO CellRun / CellRunW / H_CELL supplied by hand: everything comes from `nonvac_net`. -/
theorem audit_rv_applied :
    ∃ (v : Nat → Nat → Bool) (Rn : Run gNet v),
      ∀ n init pins, gNode n = .gate init pins → pins.contains (p 0) = true →
        pins.contains (p n) = true → n ∉ frontierL → n ∉ movL →
        ∀ t, 0 + 1 ≤ t → t ≤ 57 → Rn.exc init pins t n = gR n := by
  obtain ⟨v, Rn, hB, h1, h2, h3, h4⟩ := nonvac_net
  exact ⟨v, Rn, fun n init pins hg a b hf hm =>
    (gcd_reset_vec_net Rn hB 23 57 h1 h2 h3 h4 n init pins hg a b).1 hf hm⟩
#print axioms audit_rv_applied
#print axioms Formal.Cells.ResetGcdVec2.gcd_reset_vec_of_net
#print axioms Formal.Cells.ResetGcdVec2.cellRunW_clean
#print axioms Formal.Cells.ResetGcdVec2.cellRun_of_run
