import Formal.Target.Spec
import Formal.Cells.ArbT

/-!
# Audit T3: B's `double_ack` trace also meets the FROZEN `ArbOK` (requests only), for T ≥ 9

B's `Formal.Cells.ArbT.double_ack` proves H_ARB in B's strong form `ArbOK2` (all four
non-feedback pins) for T ≥ 7. The frozen Spec's `ArbOK` (two request nodes only) is a
different hypothesis; here: the same q/r1/r2 waveforms satisfy the frozen `ArbOK T` for every
`T ≥ 9`. So the double acknowledge (both clients acknowledged in one server transaction) is
also allowed by the frozen H_ARB(T): H_ARB(T) as frozen does not give arbiter safety either.
(The gates in B's trace are B's `RGate` relation, not the frozen `GateOK`; not re-proved here.)
-/

open Formal.Target

namespace Audit.T3.DA

def xda : Beh := fun n => if n = 1 then Formal.Cells.ArbT.cr1 else if n = 2 then Formal.Cells.ArbT.cr2
  else Formal.Cells.ArbT.cq

theorem frozen_arbOK (T : Nat) (hT : 9 ≤ T) : ArbOK T [⟨1, 2, 3⟩] xda := by
  intro a ha t1 t2 _ h2 t ht1 ht2
  simp only [List.mem_singleton] at ha
  subst ha
  have e2 : ∀ s, xda 2 s = Formal.Cells.ArbT.cr2 s := fun s => rfl
  have e3 : ∀ s, xda 3 s = Formal.Cells.ArbT.cq s := fun s => rfl
  show xda 3 t = xda 3 (t1 + T)
  rw [e3, e3]
  by_cases hlate : 11 ≤ t1
  · simp only [Formal.Cells.ArbT.cq]
    simp [show ¬ (t < 20) by omega, show ¬ (t1 + T < 20) by omega]
  · by_cases hearly : t2 ≤ 10
    · simp only [Formal.Cells.ArbT.cq]
      simp [show ¬ (11 ≤ t) by omega, show ¬ (11 ≤ t1 + T) by omega]
    · exfalso
      have := h2 11 (by omega) (by omega)
      change xda 2 11 = xda 2 t1 at this
      rw [e2, e2] at this
      simp [Formal.Cells.ArbT.cr2] at this
      omega

/-- With B's lemma: in the same trace both acknowledges rise during one transaction. -/
theorem double_ack_frozen (T : Nat) (hT : 9 ≤ T) :
    ArbOK T [⟨1, 2, 3⟩] xda ∧ Formal.Cells.ArbT.cA1 19 = true ∧ Formal.Cells.ArbT.cA2 20 = true ∧
      Formal.Cells.ArbT.cR0 12 = true :=
  ⟨frozen_arbOK T hT, (Formal.Cells.ArbT.double_ack 7 le_rfl).2.2.2.2.1,
   (Formal.Cells.ArbT.double_ack 7 le_rfl).2.2.2.2.2.2.1, rfl⟩

/-- Negative control: for T = 8 the frozen ArbOK FAILS on this trace (q moves at step
19 -> 20, more than 8 after the last request edge at 10 -> 11). -/
theorem frozen_arbOK_8_fails : ¬ ArbOK 8 [⟨1, 2, 3⟩] xda := by
  intro h
  have := h ⟨1, 2, 3⟩ (by simp) 11 20 (fun t h1 _ => by simp [xda, Formal.Cells.ArbT.cr1] <;> omega)
    (fun t h1 _ => by simp [xda, Formal.Cells.ArbT.cr2] <;> omega) 20 (by omega) le_rfl
  simp [xda, Formal.Cells.ArbT.cq] at this

end Audit.T3.DA
