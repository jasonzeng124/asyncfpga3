import Formal.Net.GcdHwLib
open Formal.Net.GcdHw
theorem sel_ite (p : Prop) [Decidable p] (a b : Nat) : Ops.select (if p then 1 else 0) a b = if p then a else b := by
  by_cases h : p <;> simp [h, Ops.select]
section
variable (w a b : Nat)
theorem c_sgt : Ops.cmpi .sgt w a b = if Ops.flip w b < Ops.flip w a then 1 else 0 := by
  simp only [Ops.cmpi, Ops.b2n]; by_cases h : Ops.flip w b < Ops.flip w a <;> simp [h]
end
example (a b : Nat) : Ops.select (Ops.cmpi .sgt 32 a b) a b = 0 := by
  simp only [c_sgt, sel_ite]
  trace_state
  sorry
example (a b : Nat) : Ops.select (Ops.cmpi .sgt 32 a b) a b = 0 := by
  simp only [c_sgt, sel_ite, Ops.flip]
  trace_state
  sorry
example (a b : Nat) : Ops.select (Ops.cmpi .sgt 32 (Ops.subi 32 a b) 4294967295) a b = 0 := by
  simp only [c_sgt, sel_ite, Ops.flip, Ops.subi]
  trace_state
  sorry
example (a b : Nat) : Ops.select (Ops.cmpi .sgt 32 (Ops.subi 32 a b) 4294967295) a b = 0 := by
  simp only [c_sgt, sel_ite, Ops.flip, Ops.subi, Nat.reducePow]
  trace_state
  sorry
