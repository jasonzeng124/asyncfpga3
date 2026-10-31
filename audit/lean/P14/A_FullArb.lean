import Formal.Core.XAudit.Events9FullArb

/-!
P14 audit (A): Events9FullArb (commits d0796d93 / 2f2fa92f).

1. The theorems take ONE `T0` for all arbiters (`hrows : ∀ k, ArbRowsOK d (as k) T T0`), while
   `xarbnet` decides `ArbRowsOK` per arbiter at its own `t0Min`. `rows_mono` shows the decided
   instances lift to the common `T0 := max`, so the checker's per-arbiter evaluation does
   discharge the theorem's `hrows` (ArbRowsOK is upward-closed in `T0`).
2. The statements and their hypothesis lists, printed for the record (#check).
3. Axiom audit of both verdicts.
-/

open Formal.Core.XAudit.Events9ArbNet

namespace AuditP14A

theorem rows_mono {N : Nat} {d : Formal.Core.XAudit.Design} {a : ArbD N} {T T0 T0' : Nat}
    (h : ArbRowsOK d a T T0) (hle : T0 ≤ T0') : ArbRowsOK d a T T0' := by
  unfold ArbRowsOK at *
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, by omega, by omega, by omega, by omega, by omega, by omega, h11, h12, h13⟩

end AuditP14A

#check @Formal.Core.XAudit.Events9FullArb.design_verdict9arbnet_edge
#check @Formal.Core.XAudit.Events9ArbNet.ArbEdge
#print axioms Formal.Core.XAudit.Events9FullArb.design_verdict9_full_arb
#print axioms Formal.Core.XAudit.Events9FullArb.design_verdict9arbnet_edge
#print axioms Formal.Core.XAudit.Events9ArbNet.arbCond_of_edge
#print axioms Formal.Core.XAudit.Events9ArbNet.grant_fall_after_req_fall
