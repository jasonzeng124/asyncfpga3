import Formal.Net.CellBindOps

/-!
# Probe C-witgen (finding): what O4's chain hypotheses actually say

O4's `GenChain i o` (H_CHAIN_SETTLED) and `GenBufChain i o` (H_REQ_PERSIST) quantify the
chain's stages EXISTENTIALLY (number, kind, wiring). Taking the one-stage decomposition
(x0 = i, x1 = o, a LUT1 buffer) shows:

* **`genChain_iff`**: `GenChain i o` holds iff `o` moves only to `i`'s previous value (the
  lumped Ops node, e.g. `Link.H_ACK_DI`), `i` changes only when `o` already shows it (end-only
  persistence), and `o 0 = i 0`.
* **`genBufChain_iff`**: the same for `GenBufChain`.

So the chain part of H_GEN is the lumped Ops field plus end-only persistence, restated; it does
NOT require bdc's own stages to have settled. It is falsified by a runt at the chain output
(O4's `fastfall_hazard` run violates the lumped property), not by an unsettled internal stage:
the negative control `Wip/Cwitgen/neg/NegSettled.lean` is a run in which bdc's `uack` chain of
one link is unsettled, which the fixed-decomposition checker rejects, yet which satisfies
`GenChain` through the one-stage decomposition (checked there too).
-/

namespace Formal.Net.CellBind.GenWit
open Formal.Net Formal.Net.CellBind Formal.Net.CellBind.Ops Formal.Net.CellBind.Chain
open Formal.Gen Formal.Gen.Cells Formal.Net.Ops.Gen

/-- The one-stage decomposition. -/
def x1 (i o : Trace) (k : Nat) : Trace := if k = 0 then i else o

theorem genChain_iff {i o : Trace} :
    GenChain i o ↔ (∀ t, o (t + 1) ≠ o t → o (t + 1) = i t) ∧ (∀ t, i (t + 1) ≠ i t → o t = i t) ∧
      o 0 = i 0 := by
  constructor
  · intro h
    refine ⟨chain_lumped h, ?_, ?_⟩
    · obtain ⟨n, st, x, hn, h0, hN, _, _, hS, _⟩ := h
      intro t ht
      rw [← h0] at ht ⊢; rw [← hN]
      exact hS t ht n (Nat.le_refl n)
    · obtain ⟨n, st, x, hn, h0, hN, _, _, _, hI⟩ := h
      rw [← h0, ← hN]; exact hI n (Nat.le_refl n)
  · rintro ⟨hL, hP, h0⟩
    refine ⟨1, fun _ => .buf 0, x1 i o, Nat.le_refl 1, rfl, rfl, fun _ _ _ => Nat.zero_le 1, ?_, ?_, ?_⟩
    · intro k hk1 hk t hm
      obtain rfl : k = 1 := by omega
      simp only [x1, Stage.G, (sym_gate _).1] at hm ⊢
      exact hL t hm
    · intro t ht j hj
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · rfl
      · simp only [x1] at ht ⊢; exact hP t ht
    · intro j hj
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · rfl
      · simp only [x1]; exact h0

theorem genBufChain_iff {i o : Trace} :
    GenBufChain i o ↔ (∀ t, o (t + 1) ≠ o t → o (t + 1) = i t) ∧ (∀ t, i (t + 1) ≠ i t → o t = i t) ∧
      o 0 = i 0 := by
  constructor
  · intro h
    refine ⟨bufchain_lumped h, ?_, ?_⟩
    · obtain ⟨n, x, hn, h0, hN, _, hP, _⟩ := h
      intro t ht
      rw [← h0] at ht ⊢; rw [← hN]
      exact hP t ht
    · obtain ⟨n, x, hn, h0, hN, _, _, hI⟩ := h
      rw [← h0, ← hN]; exact hI n (Nat.le_refl n)
  · rintro ⟨hL, hP, h0⟩
    refine ⟨1, x1 i o, Nat.le_refl 1, rfl, rfl, ?_, ?_, ?_⟩
    · intro k hk1 hk t hm
      obtain rfl : k = 1 := by omega
      simp only [x1, (sym_gate _).1] at hm ⊢
      exact hL t hm
    · intro t ht
      simp only [x1] at ht ⊢; exact hP t ht
    · intro j hj
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · rfl
      · simp only [x1]; exact h0

end Formal.Net.CellBind.GenWit
