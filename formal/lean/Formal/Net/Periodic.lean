import Formal.Target.Spec
import Formal.Timing.SpecSettle

/-!
# Eventually periodic behaviours (shard C, 2026-11-07)

**Problem, plainly.** Some candidate counterexamples to THE statement never go quiet: a ring of LUTs keeps
oscillating for ever and the result never comes out (a livelock). A finite list of transition times cannot describe
such a run, so the per-gate checks used for the deadlock refutations do not apply. If the run is *eventually
periodic* (from `t0` on, every node repeats with period `Q`), it is still finite data.

**Proved.** `sigQ (v0, A, B)` is the signal with initial value `v0`, transitions at the times in `A` (all `< t0`) and
at `p + k·Q` for every `p ∈ B` (all in `[t0, t0 + Q)`) and every `k`. `sigQ_periodic`: if `B` has even length, then
`sigQ c (t + Q) = sigQ c t` for `t ≥ t0`. `sigQ_unroll`: below `t0 + 2Q` it equals the finite signal with
transitions `A ++ B ++ B.map (· + Q)`. `gateOK_of_periodic`: if a gate with transport read delays `d i ≤ Q` satisfies
the gate equation at every `t ∈ [start, t0 + 2Q)` and every node's signal is `Q`-periodic from `t0`, it satisfies it
at every `t ≥ start` (induction on `t` in steps of `Q`).

**Not shown here.** Any particular run (data), the environment or arbiter clauses.
-/

namespace Formal.Net.Periodic
open Formal.Target

/-- A finite code: initial value and transition times (as in the deadlock witnesses). -/
def sigF (v0 : Bool) (ts : List Nat) : Sig := fun t => v0 != ((ts.countP fun x => decide (x ≤ t)) % 2 == 1)

/-- The number of transitions `p + k·Q ≤ t`, `k ≥ 0`, contributed by one periodic time `p`. -/
def cnt1 (Q p t : Nat) : Nat := if p ≤ t then (t - p) / Q + 1 else 0

/-- An eventually periodic code: initial value, prefix transitions `A`, one period of transitions `B`. -/
def sigQ (Q : Nat) (v0 : Bool) (A B : List Nat) : Sig := fun t =>
  v0 != (((A.countP fun x => decide (x ≤ t)) + (B.map fun p => cnt1 Q p t).sum) % 2 == 1)

theorem cnt1_shift {Q p t t0 : Nat} (hQ : 0 < Q) (hp1 : t0 ≤ p) (hp2 : p < t0 + Q) (ht : t0 ≤ t) :
    cnt1 Q p (t + Q) = cnt1 Q p t + 1 := by
  unfold cnt1
  by_cases h : p ≤ t
  · rw [if_pos (by omega), if_pos h]
    rw [show t + Q - p = (t - p) + Q by omega, Nat.add_div_right _ hQ]
  · rw [if_pos (by omega), if_neg h]
    have : (t + Q - p) / Q = 0 := Nat.div_eq_of_lt (by omega)
    omega

theorem sum_shift {Q t0 : Nat} (hQ : 0 < Q) (t : Nat) (ht : t0 ≤ t) :
    ∀ B : List Nat, (∀ p ∈ B, t0 ≤ p ∧ p < t0 + Q) →
      (B.map fun p => cnt1 Q p (t + Q)).sum = (B.map fun p => cnt1 Q p t).sum + B.length
  | [], _ => by simp
  | p :: B, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [cnt1_shift hQ (h p List.mem_cons_self).1 (h p List.mem_cons_self).2 ht,
      sum_shift hQ t ht B (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    omega

theorem countP_le_of_lt {t0 t : Nat} (ht : t0 ≤ t) (s : Nat) :
    ∀ A : List Nat, (∀ a ∈ A, a < t0) →
      (A.countP fun x => decide (x ≤ t + s)) = A.countP fun x => decide (x ≤ t)
  | [], _ => rfl
  | a :: A, h => by
    have ha := h a List.mem_cons_self
    simp only [List.countP_cons]
    rw [countP_le_of_lt ht s A (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    have e1 : decide (a ≤ t + s) = true := by simp; omega
    have e2 : decide (a ≤ t) = true := by simp; omega
    rw [e1, e2]

/-- **Periodicity** from `t0` on, when one period has an even number of transitions. -/
theorem sigQ_periodic {Q t0 : Nat} (hQ : 0 < Q) {v0 : Bool} {A B : List Nat} (hA : ∀ a ∈ A, a < t0)
    (hB : ∀ p ∈ B, t0 ≤ p ∧ p < t0 + Q) (he : B.length % 2 = 0) {t : Nat} (ht : t0 ≤ t) :
    sigQ Q v0 A B (t + Q) = sigQ Q v0 A B t := by
  unfold sigQ
  rw [countP_le_of_lt ht Q A hA, sum_shift hQ t ht B hB]
  congr 2
  omega

theorem cnt1_lt_two {Q p t t0 : Nat} (hQ : 0 < Q) (hp1 : t0 ≤ p) (ht : t < t0 + 2 * Q) :
    cnt1 Q p t = (if p ≤ t then 1 else 0) + (if p + Q ≤ t then 1 else 0) := by
  unfold cnt1
  by_cases h1 : p ≤ t
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : p + Q ≤ t
    · rw [if_pos h2, Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    · rw [if_neg h2, Nat.div_eq_of_lt_le (k := 0) (by omega) (by omega)]
  · rw [if_neg h1, if_neg h1, if_neg (by omega)]

theorem countP_append_le (t : Nat) (l m : List Nat) :
    ((l ++ m).countP fun x => decide (x ≤ t)) = (l.countP fun x => decide (x ≤ t)) + m.countP fun x => decide (x ≤ t) :=
  List.countP_append

theorem sum_two {Q t0 t : Nat} (hQ : 0 < Q) (ht : t < t0 + 2 * Q) :
    ∀ B : List Nat, (∀ p ∈ B, t0 ≤ p) →
      (B.map fun p => cnt1 Q p t).sum =
        (B.countP fun x => decide (x ≤ t)) + ((B.map (· + Q)).countP fun x => decide (x ≤ t))
  | [], _ => by simp
  | p :: B, h => by
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    rw [cnt1_lt_two hQ (h p List.mem_cons_self) ht, sum_two hQ ht B (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    by_cases h1 : p ≤ t <;> by_cases h2 : p + Q ≤ t <;> simp [h1, h2] <;> omega

/-- **Unrolling**: below `t0 + 2Q` the periodic code is the finite code with two copies of the period. -/
theorem sigQ_unroll {Q t0 : Nat} (hQ : 0 < Q) {v0 : Bool} {A B : List Nat} (hB : ∀ p ∈ B, t0 ≤ p) {t : Nat}
    (ht : t < t0 + 2 * Q) : sigQ Q v0 A B t = sigF v0 (A ++ B ++ B.map (· + Q)) t := by
  unfold sigQ sigF
  rw [countP_append_le, countP_append_le, sum_two hQ ht B hB, Nat.add_assoc]

/-- **The gate relation from two periods.** For transport reads `t - d i` with `d i ≤ Q`: if the gate equation holds
at every `t ∈ [s, t0 + 2Q)` and every node is `Q`-periodic from `t0`, it holds at every `t ≥ s`. -/
theorem eq_of_periodic {Q t0 s : Nat} (hQ : 0 < Q) {x : Beh} {g : Gate} {d : Nat → Nat}
    (hd : ∀ i, i < g.k → d i ≤ Q) (hs : s ≤ t0 + Q)
    (hper : ∀ n t, t0 ≤ t → x n (t + Q) = x n t)
    (hfin : ∀ t, s ≤ t → t < t0 + 2 * Q →
      x g.out t = g.init.testBit (addr g.k fun i => x (g.ins.getD i 0) (t - d i))) :
    ∀ t, s ≤ t → x g.out t = g.init.testBit (addr g.k fun i => x (g.ins.getD i 0) (t - d i)) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro hst
    by_cases ht : t < t0 + 2 * Q
    · exact hfin t hst ht
    · have e := ih (t - Q) (by omega) (by omega)
      have e1 : x g.out t = x g.out (t - Q) := by
        have := hper g.out (t - Q) (by omega); rwa [show t - Q + Q = t by omega] at this
      rw [e1, e]
      congr 1
      apply Formal.Timing.SpecSettle.addr_congr
      intro i hi
      have := hd i hi
      have h2 := hper (g.ins.getD i 0) (t - Q - d i) (by omega)
      rw [show t - Q - d i + Q = t - d i by omega] at h2
      exact h2.symm

end Formal.Net.Periodic
