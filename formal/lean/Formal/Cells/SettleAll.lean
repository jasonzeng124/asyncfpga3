import Formal.Cells.ForceTree

/-!
# Formal.Cells.SettleAll — value-independent settling windows of a fully evaluated acyclic island (shard B, 2026-11-19)

**Problem, plainly.** To prove that a bundled-data capture is SAFE (a lower bound on its margin, PROGRAM's kappa_lo),
the data side needs an UPPER bound on when the captured combinational logic has settled, valid for every operand.
`ForceTree.force_tree` gives value windows when forcing pin sets are known per value; for a data path the values depend
on the operands. Here every gate is forced by ALL its pins at their evaluated values, which always forces its INIT: so
the window of each node depends only on the windows of its inputs and the pins' delay bounds, not on the values.

**Proved.**
* `forcesP_all`: a gate's full assignment (every pin at a value) forces its INIT to the INIT's bit at that address.
* `settle_all`: an acyclic island (ranked) whose gates' outputs are any CONSISTENT valuation `val` (each gate's value
  is its INIT at its pins' sources' values) and whose roots hold `val` on their windows: every node shows `val w` on
  `[a w, b w]` whenever `a src + U ≤ a w` and `b w ≤ b src + L` for every pin. The windows are the usual longest /
  shortest path recurrences and do not mention `val`, so one window computation serves every operand.

**Not shown.** The windows of a real route (computed by an untrusted script from the decoded arcs); that the island of a
real route is acyclic (the script checks it); which valuation the circuit takes (any consistent one is covered).
-/

namespace Formal.Cells.SettleAll
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Timing.SpecLoop Formal.Timing.Island
  Formal.Cells.ForceTree

theorem eq_addr_of_bits (k a : Nat) (v : Nat → Bool) (ha : a < 2 ^ k) (hb : ∀ j, j < k → a.testBit j = v j) :
    a = addr k v := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k
  · rw [hb j hj, addr_testBit k v j hj]
  · have h1 : a < 2 ^ j := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : addr k v < 2 ^ j := lt_of_lt_of_le (addr_lt k v) (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

/-- **A full assignment forces the INIT bit at its address.** -/
theorem forcesP_all (k init : Nat) (v : Nat → Bool) :
    ForcesP k init ((List.range k).map fun j => (j, v j)) (init.testBit (addr k v)) = true := by
  simp only [ForcesP, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
  intro a ha
  by_cases h : ((List.range k).map fun j => (j, v j)).all (fun e => a.testBit e.1 == e.2) = true
  · right
    simp only [List.all_eq_true, List.mem_map, List.mem_range, beq_iff_eq] at h
    have hb : ∀ j, j < k → a.testBit j = v j := fun j hj => h (j, v j) ⟨j, hj, rfl⟩
    rw [eq_addr_of_bits k a v ha hb]
  · left; simpa using h

/-- **Settling windows of a fully evaluated acyclic island, for any consistent valuation.** -/
theorem settle_all {p : DelayPar} {c : ℚ} {x : Beh}
    (comb root : Nat → Prop) (ρ : Nat → Nat) (gate : Nat → Gate) (src : Nat → Nat → Nat)
    (arcs : Nat → Nat → List Arc) (S : Nat → Nat) (val : Nat → Bool)
    (L U : Nat → Nat → Nat) (a b : Nat → Nat)
    (hg : ∀ w, comb w → (gate w).out = w ∧ CGateOK p c (gate w) (src w) (arcs w) (S w) x)
    (hLU : ∀ w, comb w → ∀ j, j < (gate w).k → ∀ D, SumAdm p c (arcs w j) D → L w j ≤ D ∧ D ≤ U w j)
    (hval : ∀ w, comb w → val w = (gate w).init.testBit (addr (gate w).k fun j => val (src w j)))
    (hps : ∀ w, comb w → ∀ j, j < (gate w).k → root (src w j) ∨ (comb (src w j) ∧ ρ (src w j) < ρ w))
    (hwin : ∀ w, comb w → ∀ j, j < (gate w).k → a (src w j) + U w j ≤ a w ∧ b w ≤ b (src w j) + L w j)
    (hS : ∀ w, comb w → S w ≤ a w)
    (hroot : ∀ r, root r → ∀ t, a r ≤ t → t ≤ b r → x r t = val r) :
    ∀ w, comb w → ∀ t, a w ≤ t → t ≤ b w → x w t = val w := by
  refine force_tree comb root ρ gate src arcs S val (fun w => List.range (gate w).k) L U a b hg hLU ?_ ?_ ?_ hS hroot
  · intro w hw
    have := forcesP_all (gate w).k (gate w).init (fun j => val (src w j))
    rw [← hval w hw] at this
    simpa [asgOf] using this
  · intro w hw j hj; rw [List.mem_range] at hj; exact ⟨hj, hps w hw j hj⟩
  · intro w hw j hj; rw [List.mem_range] at hj; exact hwin w hw j hj

end Formal.Cells.SettleAll
