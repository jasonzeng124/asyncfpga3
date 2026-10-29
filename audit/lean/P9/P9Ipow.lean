import Formal.Cells.IpowCells
/-! P9 audit, item 3. -/
namespace P9Ipow
open Formal.Net Formal.Net.Handshake Formal.Net.CapNet Formal.Cells.IpowCells
#check @ipow_safe_of_contracts
#print axioms ipow_safe_of_contracts
#print axioms ipow_cells
#print axioms ipow_contracts_satisfiable
#print axioms fbCel_witness
#print axioms ctree_atomic_only_select

/-- The all-quiet witness latches nothing: the conclusion of ipow_safe_of_contracts is
vacuous on it (my check). -/
theorem quiet_no_token (dv : Fin NC → Nat) : ∀ k v, ¬ TokAt (chQ dv out0) k v := by
  intro k v h; exact absurd h.1 (by simp [fallB, chQ])

/-- Mutation: the quiet data solution is specific to (b, e) = (3, 7). -/
theorem mut_data : ¬ (∀ o : Fin NO, DataOK (srcV 3 8) dvW (opAt o)) := by decide +kernel
end P9Ipow
