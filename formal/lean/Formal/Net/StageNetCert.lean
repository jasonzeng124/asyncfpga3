import Formal.Net.StageNet

/-!
# A checkable certificate of "no trap" for a stage network (shard C, 2026-11-18)

**Problem, plainly.** `StageNet.deadlock_free` / `fair_all_fire` need "the state has no trap"
(no closed walk of token-free arcs). For a concrete network exported from a design that is a
finite graph question; this file turns it into a certificate Lean can check by `decide`:
a rank on the stages that strictly increases along every token-free arc. A rank exists iff the
token-free arcs form no cycle, i.e. iff there is no trap (only the direction we need,
rank => no trap, is proved).

* `no_trap_of_rank`: a strictly increasing rank along `Z` rules out every trap.
* `Cert` / `Cert.check`: a network on `Fin n` given as an edge list, a state and a rank, and
  a Boolean checker. `Cert.check_sound`: `check = true` implies no trap, hence (by
  `StageNet.deadlock_free`) no reachable deadlock and (by `fair_all_fire`) every stage firing
  infinitely often in every weakly fair run.

What it does NOT say: that the certificate's graph and state are the circuit's (the exporter
is untrusted), anything about mode changes, or anything outside the stage model's hypotheses
(see `StageNet`'s header: H_RENDEZVOUS).
-/

namespace Formal.Net.StageNet

variable {V : Type}

theorem no_trap_of_rank (E : V → V → Prop) (x : State V) (r : V → Nat)
    (hr : ∀ a b, Z E x a b → r a < r b) : ¬ HasTrap E x := by
  rintro ⟨S, ⟨v, hv⟩, hS⟩
  -- the least rank attained in S
  have hex : ∃ k, ∃ u, S u ∧ r u = k := ⟨r v, v, hv, rfl⟩
  have key : ∀ k, ∀ u, S u → r u = k → False := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro u hu hk
      obtain ⟨a, ha, hz⟩ := hS u hu
      exact ih (r a) (hk ▸ hr a u hz) a ha rfl
  obtain ⟨k, u, hu, hk⟩ := hex
  exact key k u hu hk

/-- A concrete network: `n` stages, edges `p → t` ("p feeds t"), a state and a rank. -/
structure Cert where
  n : Nat
  edges : List (Nat × Nat)
  x : List Bool
  rank : List Nat

namespace Cert

def E (c : Cert) (p t : Fin c.n) : Prop := (p.val, t.val) ∈ c.edges
def st (c : Cert) : State (Fin c.n) := fun i => c.x.getD i.val false
def rk (c : Cert) (i : Fin c.n) : Nat := c.rank.getD i.val 0

/-- Every edge has both ends in range, and its token-free arc goes up in rank. -/
def check (c : Cert) : Bool :=
  c.edges.all fun (p, t) =>
    decide (p < c.n) && decide (t < c.n) &&
      (if c.x.getD p false == c.x.getD t false then
         decide (c.rank.getD p 0 < c.rank.getD t 0)
       else decide (c.rank.getD t 0 < c.rank.getD p 0))

theorem check_sound (c : Cert) (h : c.check = true) : ¬ HasTrap c.E c.st := by
  apply no_trap_of_rank c.E c.st c.rk
  intro a b hz
  unfold check at h
  rw [List.all_eq_true] at h
  rcases hz with ⟨he, hx⟩ | ⟨he, hx⟩
  · have h1 := h _ he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨_, h3⟩ := h1
    have hb : (c.x.getD a.val false == c.x.getD b.val false) = true := beq_iff_eq.mpr hx
    simp only [hb, ↓reduceIte, decide_eq_true_eq] at h3
    exact h3
  · have h1 := h _ he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨_, h3⟩ := h1
    have hb : (c.x.getD b.val false == c.x.getD a.val false) = false := by
      cases hq : (c.x.getD b.val false == c.x.getD a.val false)
      · rfl
      · exact absurd (beq_iff_eq.mp hq) hx
    rw [hb] at h3
    simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at h3
    exact h3

end Cert

/-- Two-stage ring with one token: dead (sanity: a trap, so no certificate exists). -/
example : Cert.check ⟨2, [(0, 1), (1, 0)], [true, false], [0, 1]⟩ = false := by decide

/-- Three-stage ring with one token (`resetState 1`): certified. -/
example : Cert.check ⟨3, [(0, 1), (1, 2), (2, 0)], [true, false, false], [1, 0, 2]⟩ = true := by
  decide

end Formal.Net.StageNet
