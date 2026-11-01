import Formal.Target.Spec
import Formal.Cells.SpecArbVacuous
import Formal.Cells.ArbT
import Formal.Cells.HPrimInv

/-! Audit T3: axioms of shard B's theorems cited in T3.md (kernel facts, not their check.sh). -/

#print axioms Formal.Cells.SpecArbVacuous.arbOK_excludes_handover
#print axioms Formal.Cells.SpecArbVacuous.handover_gate_ok
#print axioms Formal.Cells.SpecArbVacuous.arbOK_vacuous_for_every_T
#print axioms Formal.Cells.ArbT.double_ack
#print axioms Formal.Cells.ArbT.cex_gates
#print axioms Formal.Cells.ArbT.one_ack
#print axioms Formal.Cells.HPrimInv.rat_not_win
#print axioms Formal.Cells.HPrimInv.rat_not_readTime
#print axioms Formal.Cells.HPrimInv.inv_sep_win

-- the statement B's main lemma proves, restated with the frozen names (elaborates only if identical)
example : ∀ (p : Formal.Target.DelayPar) (c : ℚ) (g : Formal.Target.Gate) (x : Formal.Target.Beh)
    (r1 r2 q rst a0 T ta : Nat), g.k = 5 → g.ins = [r1, r2, q, rst, a0] → g.init = 0xFFF0FFB2 →
    g.out = q → Formal.Target.GateOK p c g x → (∀ t, x r1 t = false) → (∀ t, x r2 t = true) →
    (∀ t, x rst t = false) → (∀ t, x a0 t = decide (t < ta)) → x q T = true →
    Formal.Target.ArbOK T [⟨r1, r2, q⟩] x → False :=
  fun p c g x r1 r2 q rst a0 T ta => Formal.Cells.SpecArbVacuous.arbOK_excludes_handover p c g x r1 r2 q rst a0 T ta
