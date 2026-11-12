import Formal.Timing.SpecLoop

/-!
# Self-confirming islands (shard C)

**Problem, plainly.** After reset, an idle circuit should stay idle whatever its unreset storage
(data latches, arbiter states) holds. In the Spec's semantics a node may depend on such nodes, so
plain settling (which needs every input's value) does not apply. A **partial forcing** says: some
pins at given values force the INIT whatever the others read (`ForcesP`). An **island** is a set of
nodes with values such that every gate member is forced to its value by pins whose sources are
members (or environment nodes with guaranteed values).

**Proved.**
* `forcesP_sound`: a partial forcing fixes the output for every completion of the pin values.
* `settle_partial`: ranked combinational members over roots that hold their values on `[A, B]`
  hold theirs on `[A + (ρ w + 1)·M, B]` (settle_value with partial forcing).
* `island_forever`: if every gate member holds its value on `[T - M, T]`, the environment members
  hold theirs from `T - M` on, every forcing pin's composite delay is at least 1 ps and at most `M`,
  then every member holds its value for ever (from `T - M`).
-/

namespace Formal.Timing.Island
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Timing.SpecLoop

/-- The pins listed in `asg` at their listed values force `init` to `q`. -/
def ForcesP (k init : Nat) (asg : List (Nat × Bool)) (q : Bool) : Bool :=
  (List.range (2 ^ k)).all fun a => !(asg.all fun e => a.testBit e.1 == e.2) || (init.testBit a == q)

theorem forcesP_sound {k init : Nat} {asg : List (Nat × Bool)} {q : Bool} (h : ForcesP k init asg q = true)
    (v : Nat → Bool) (hv : ∀ e ∈ asg, e.1 < k ∧ v e.1 = e.2) : init.testBit (addr k v) = q := by
  simp only [ForcesP, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at h
  rcases h _ (addr_lt k v) with h | h
  · exfalso
    simp only [List.all_eq_false, beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨e, he, hne⟩ := h
    obtain ⟨h1, h2⟩ := hv e he
    exact hne (by rw [addr_testBit _ _ _ h1, h2]; simp)
  · exact h

/-- The assignment of gate `w`'s forcing pins `ps` to the values of their sources. -/
def asgOf (src : Nat → Nat → Nat) (val : Nat → Bool) (w : Nat) (ps : List Nat) : List (Nat × Bool) :=
  ps.map fun j => (j, val (src w j))

/-- **Settling with partial forcing.** -/
theorem settle_partial {p : DelayPar} {c : ℚ} {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (comb root : Nat → Prop) (ρ : Nat → Nat) (gate : Nat → Gate) (src : Nat → Nat → Nat)
    (arcs : Nat → Nat → List Arc) (S : Nat → Nat) (M A B : Nat) (val : Nat → Bool) (ps : Nat → List Nat)
    (hg : ∀ w, comb w → (gate w).out = w ∧ CGateOK p c (gate w) (src w) (arcs w) (S w) x)
    (hord : ∀ w, comb w → ∀ i, i < (gate w).k → ArcsOrd (arcs w i))
    (hF : ∀ w, comb w → ForcesP (gate w).k (gate w).init (asgOf src val w (ps w)) (val w) = true)
    (hps : ∀ w, comb w → ∀ j ∈ ps w, j < (gate w).k ∧
      (root (src w j) ∨ (comb (src w j) ∧ ρ (src w j) < ρ w)))
    (hM : ∀ w, comb w → ∀ i, i < (gate w).k → sumMax p (arcs w i) ≤ M)
    (hS : ∀ w, comb w → S w ≤ A)
    (hroot : ∀ r, root r → ∀ t, A ≤ t → t ≤ B → x r t = val r) :
    ∀ w, comb w → ∀ t, A + (ρ w + 1) * M ≤ t → t ≤ B → x w t = val w := by
  intro w
  induction hr : ρ w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    intro hw t h1 h2
    obtain ⟨hout, F, -, hFt⟩ := hg w hw
    obtain ⟨hrd, ho⟩ := hFt t (by have := hS w hw; have : M ≤ (n + 1) * M := Nat.le_mul_of_pos_left _ (by omega); omega)
    suffices hv : ∀ e ∈ asgOf src val w (ps w), e.1 < (gate w).k ∧ x (src w e.1) (F e.1 t) = e.2 by
      have := forcesP_sound (hF w hw) (fun i => x (src w i) (F i t)) hv
      rw [hout] at ho; rw [ho]; exact this
    intro e he
    simp only [asgOf, List.mem_map] at he
    obtain ⟨j, hj, rfl⟩ := he
    dsimp only
    obtain ⟨hjk, hsrc⟩ := hps w hw j hj
    refine ⟨hjk, ?_⟩
    obtain ⟨r1, r2⟩ := hrd j hjk
    obtain ⟨b1, b2⟩ := sumAdm_bounds hp hc0 hc1 _ _ (hord w hw j hjk) r2
    have hm := hM w hw j hjk
    have hMn : M ≤ (n + 1) * M := Nat.le_mul_of_pos_left _ (by omega)
    rcases hsrc with hrt | ⟨hc, hlt⟩
    · exact hroot _ hrt _ (by omega) (by omega)
    · have : ρ (src w j) + 1 ≤ n := by omega
      have h3 := Nat.mul_le_mul_right M this
      have h4 : (n + 1) * M = n * M + M := Nat.succ_mul n M
      exact ih _ (hr ▸ hlt) _ rfl hc _ (by omega) (by omega)

/-- **A self-confirming island stays for ever.** -/
theorem island_forever {p : DelayPar} {c : ℚ} {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (mem envm : Nat → Prop) (gate : Nat → Gate) (src : Nat → Nat → Nat)
    (arcs : Nat → Nat → List Arc) (S : Nat → Nat) (M T : Nat) (hMT : M ≤ T) (val : Nat → Bool)
    (ps : Nat → List Nat)
    (hg : ∀ w, mem w → (gate w).out = w ∧ CGateOK p c (gate w) (src w) (arcs w) (S w) x)
    (hord : ∀ w, mem w → ∀ i, i < (gate w).k → ArcsOrd (arcs w i))
    (hF : ∀ w, mem w → ForcesP (gate w).k (gate w).init (asgOf src val w (ps w)) (val w) = true)
    (hps : ∀ w, mem w → ∀ j ∈ ps w, j < (gate w).k ∧ (mem (src w j) ∨ envm (src w j)) ∧
      1 ≤ sumMin p (arcs w j) ∧ sumMax p (arcs w j) ≤ M)
    (hS : ∀ w, mem w → S w ≤ T - M)
    (henv : ∀ e, envm e → ∀ t, T - M ≤ t → x e t = val e)
    (hbase : ∀ w, mem w → ∀ t, T - M ≤ t → t ≤ T → x w t = val w) :
    ∀ w, mem w → ∀ t, T - M ≤ t → x w t = val w := by
  intro w hw t
  induction t using Nat.strong_induction_on generalizing w with
  | _ t ih =>
    intro ht
    by_cases htT : t ≤ T
    · exact hbase w hw t ht htT
    obtain ⟨hout, F, -, hFt⟩ := hg w hw
    obtain ⟨hrd, ho⟩ := hFt t (by have := hS w hw; omega)
    suffices hv : ∀ e ∈ asgOf src val w (ps w), e.1 < (gate w).k ∧ x (src w e.1) (F e.1 t) = e.2 by
      have := forcesP_sound (hF w hw) (fun i => x (src w i) (F i t)) hv
      rw [hout] at ho; rw [ho]; exact this
    intro e he
    simp only [asgOf, List.mem_map] at he
    obtain ⟨j, hj, rfl⟩ := he
    dsimp only
    obtain ⟨hjk, hsrc, hmin, hmax⟩ := hps w hw j hj
    refine ⟨hjk, ?_⟩
    obtain ⟨r1, r2⟩ := hrd j hjk
    obtain ⟨b1, b2⟩ := sumAdm_bounds hp hc0 hc1 _ _ (hord w hw j hjk) r2
    rcases hsrc with hm | he'
    · exact ih _ (by omega) _ hm (by omega)
    · exact henv _ he' _ (by omega)

end Formal.Timing.Island
