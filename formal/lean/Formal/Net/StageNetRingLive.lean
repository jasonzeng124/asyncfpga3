import Formal.Net.StageNet

/-!
# When is a ring of stages live? (shard C, 2026-11-18)

**Problem, plainly.** bdc's suite found that a loop compiled to a ring deadlocks when the ring
holds as many tokens as it has room for (kernel `quadrec`), and research's token floor
(`research/data/suite/ringfloor.md`) adds stages until a ring of `S` stages holding `T` tokens
has `S ≥ 2T + 1` (and `T ≥ 1`). This file proves the exact condition for a ring in the stage
model of `StageNet` (Muller half-buffer stages, speed independent, routing fixed).

**Model.** `n + 1` stages `0 .. n`, stage `i` feeds stage `nxt i` (the next one round the
ring). A *boundary* is an index `i` with `x i ≠ x (nxt i)`; `D x` is the number of boundaries
(the number of transitions round the ring; at a rest marking each token is two of them, so a
ring holding `T` tokens has `D = 2T`).

**Proved (no hypotheses beyond the model):**
* `ring_noTrap_iff`: the ring has no trap iff some neighbouring pair agrees and some differs.
* `ring_noTrap_iff_count`: the ring has no trap iff `0 < D x < n + 1`.
* `ring_live_tokens`: with `D x = 2T` (T tokens), no trap iff `1 ≤ T` and `2T + 1 ≤ n + 1`,
  i.e. research's `S ≥ 2T + 1` with `S = n + 1` stages, and at least one token.
With `StageNet.deadlock_free` / `fair_all_fire`, "no trap" means: no reachable deadlock and every
stage fires infinitely often in weakly fair runs; with `trap_dead`, a trap means some stage
(here: every stage of the trap) is dead forever.

**Not covered:** everything `StageNet` leaves out (H_RENDEZVOUS, mode changes, timing, data);
rings with side branches (forks / joins): those are the general `StageNet` / certificates.
-/

namespace Formal.Net.StageNet.RingLive
open Formal.Net.StageNet

variable {n : Nat}

/-- The next stage round a ring of `n + 1` stages. -/
def nxt (i : Fin (n + 1)) : Fin (n + 1) :=
  if h : i.val + 1 = n + 1 then ⟨0, by omega⟩ else ⟨i.val + 1, by omega⟩

/-- The previous stage. -/
def prv (i : Fin (n + 1)) : Fin (n + 1) :=
  if h : i.val = 0 then ⟨n, by omega⟩ else ⟨i.val - 1, by omega⟩

theorem nxt_prv (i : Fin (n + 1)) : nxt (prv i) = i := by
  apply Fin.ext
  unfold nxt prv
  by_cases h : i.val = 0
  · simp [h] <;> omega
  · simp only [h, dite_false]
    split <;> simp_all <;> omega

theorem prv_nxt (i : Fin (n + 1)) : prv (nxt i) = i := by
  apply Fin.ext
  unfold nxt prv
  by_cases h : i.val + 1 = n + 1
  · simp [h] <;> omega
  · simp only [h, dite_false]
    split <;> simp_all <;> omega

/-- The ring: stage `a` feeds stage `nxt a`. -/
def E (a b : Fin (n + 1)) : Prop := b = nxt a

/-- Going backwards round the ring from any stage reaches every stage. -/
theorem ind_prv (P : Fin (n + 1) → Prop) (hs : ∀ v, P v → P (prv v)) (a : Fin (n + 1))
    (ha : P a) : ∀ i, P i := by
  -- first a, a-1, ..., 0
  have down : ∀ m, m ≤ a.val → P ⟨a.val - m, by omega⟩ := by
    intro m
    induction m with
    | zero => intro _; simpa using ha
    | succ m ih =>
      intro hm
      have := hs _ (ih (by omega))
      have e : prv (n := n) ⟨a.val - m, by omega⟩ = ⟨a.val - (m + 1), by omega⟩ := by
        apply Fin.ext; unfold prv; split <;> simp_all <;> omega
      rwa [e] at this
  have h0 : P ⟨0, by omega⟩ := by
    have := down a.val (Nat.le_refl _); simpa using this
  -- then n, n-1, ..., down to a+1
  have hn : P ⟨n, by omega⟩ := by
    have := hs _ h0
    have e : prv (n := n) ⟨0, by omega⟩ = ⟨n, by omega⟩ := by
      apply Fin.ext; unfold prv; simp
    rwa [e] at this
  have top : ∀ m, m ≤ n → P ⟨n - m, by omega⟩ := by
    intro m
    induction m with
    | zero => intro _; simpa using hn
    | succ m ih =>
      intro hm
      have := hs _ (ih (by omega))
      have e : prv (n := n) ⟨n - m, by omega⟩ = ⟨n - (m + 1), by omega⟩ := by
        apply Fin.ext; unfold prv; split <;> simp_all <;> omega
      rwa [e] at this
  intro i
  have := top (n - i.val) (by omega)
  have e : (⟨n - (n - i.val), by omega⟩ : Fin (n + 1)) = i := by
    apply Fin.ext; simp; omega
  rwa [e] at this

/-- Going forwards round the ring from any stage reaches every stage. -/
theorem ind_nxt (P : Fin (n + 1) → Prop) (hs : ∀ v, P v → P (nxt v)) (a : Fin (n + 1))
    (ha : P a) : ∀ i, P i := by
  -- induction on the distance m from a: the stage (a + m) mod (n + 1) holds P
  have fwd : ∀ m, m ≤ n → ∀ i : Fin (n + 1), i.val = (a.val + m) % (n + 1) → P i := by
    intro m
    induction m with
    | zero =>
      intro _ i hi
      have : i = a := by
        apply Fin.ext; rw [hi]; exact Nat.mod_eq_of_lt a.isLt
      rw [this]; exact ha
    | succ m ih =>
      intro hm i hi
      have hp := hs _ (ih (by omega) (prv i) ?_)
      · rwa [nxt_prv] at hp
      · -- (prv i).val = (a + m) % (n+1)
        unfold prv
        have ha' := a.isLt
        by_cases hlt : a.val + m + 1 < n + 1
        · rw [show a.val + (m + 1) = a.val + m + 1 by omega, Nat.mod_eq_of_lt hlt] at hi
          rw [Nat.mod_eq_of_lt (by omega : a.val + m < n + 1)]
          split <;> simp_all <;> omega
        · have h2 : (a.val + (m + 1)) % (n + 1) = a.val + m + 1 - (n + 1) := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
          rw [h2] at hi
          by_cases h3 : a.val + m < n + 1
          · rw [Nat.mod_eq_of_lt h3]
            split <;> simp_all <;> omega
          · have h4 : (a.val + m) % (n + 1) = a.val + m - (n + 1) := by
              rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
            rw [h4]
            split <;> simp_all <;> omega
  intro i
  by_cases h : a.val ≤ i.val
  · exact fwd (i.val - a.val) (by omega) i (by rw [Nat.mod_eq_of_lt (by omega)]; omega)
  · refine fwd (i.val + (n + 1) - a.val) (by omega) i ?_
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- A trap of the ring forces every neighbouring pair to agree, or every pair to differ. -/
theorem trap_uniform (x : State (Fin (n + 1))) (h : HasTrap E x) :
    (∀ i, x i = x (nxt i)) ∨ (∀ i, x i ≠ x (nxt i)) := by
  obtain ⟨S, ⟨u, hu⟩, hS⟩ := h
  -- the token-free arcs into v: from prv v (if that pair agrees) or from nxt v (if v's pair differs)
  have into : ∀ a v, Z E x a v → (a = prv v ∧ x (prv v) = x v) ∨ (a = nxt v ∧ x v ≠ x (nxt v)) := by
    intro a v hz
    rcases hz with ⟨he, hx⟩ | ⟨he, hx⟩
    · left
      have : a = prv v := by unfold E at he; rw [he, prv_nxt]
      subst this; exact ⟨rfl, hx⟩
    · right
      unfold E at he; subst he; exact ⟨rfl, hx⟩
  obtain ⟨a, ha, hz⟩ := hS u hu
  rcases into a u hz with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · -- went backwards along an agreeing pair: keep going backwards, every pair agrees
    left
    have step : ∀ v, (S v ∧ x v = x (nxt v)) → (S (prv v) ∧ x (prv v) = x (nxt (prv v))) := by
      rintro v ⟨hv, hvx⟩
      obtain ⟨b, hb, hzb⟩ := hS v hv
      rcases into b v hzb with ⟨rfl, hbx⟩ | ⟨rfl, hbx⟩
      · exact ⟨hb, by rw [nxt_prv]; exact hbx⟩
      · exact absurd hvx hbx
    have all := ind_prv (fun v => S v ∧ x v = x (nxt v)) step (prv u) ⟨ha, by rw [nxt_prv]; exact hx⟩
    exact fun i => (all i).2
  · -- went forwards along a differing pair: keep going forwards, every pair differs
    right
    have step : ∀ w, (S w ∧ x (prv w) ≠ x w) → (S (nxt w) ∧ x (prv (nxt w)) ≠ x (nxt w)) := by
      rintro w ⟨hw, hwx⟩
      obtain ⟨b, hb, hzb⟩ := hS w hw
      rcases into b w hzb with ⟨rfl, hbx⟩ | ⟨rfl, hbx⟩
      · exact absurd hbx hwx
      · exact ⟨hb, by rw [prv_nxt]; exact hbx⟩
    have all := ind_nxt (fun w => S w ∧ x (prv w) ≠ x w) step (nxt u)
      ⟨ha, by rw [prv_nxt]; exact hx⟩
    intro i
    have := (all (nxt i)).2
    rwa [prv_nxt] at this

/-- **The ring has no trap iff some neighbouring pair agrees and some pair differs.** -/
theorem ring_noTrap_iff (x : State (Fin (n + 1))) :
    ¬ HasTrap E x ↔ (∃ i, x i = x (nxt i)) ∧ (∃ j, x j ≠ x (nxt j)) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · -- if every pair differs, the whole ring is a trap (each stage fed back by its successor)
      apply Classical.byContradiction
      intro hne
      apply h
      refine ⟨fun _ => True, ⟨⟨0, by omega⟩, trivial⟩, fun v _ => ⟨nxt v, trivial, ?_⟩⟩
      right
      refine ⟨rfl, ?_⟩
      intro heq
      exact hne ⟨v, heq⟩
    · -- if every pair agrees, the whole ring is a trap (each stage fed by its predecessor)
      apply Classical.byContradiction
      intro hne
      apply h
      refine ⟨fun _ => True, ⟨⟨0, by omega⟩, trivial⟩, fun v _ => ⟨prv v, trivial, ?_⟩⟩
      left
      refine ⟨by unfold E; rw [nxt_prv], ?_⟩
      have := Classical.byContradiction (fun hc => hne ⟨prv v, hc⟩)
      rwa [nxt_prv] at this
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ h
    rcases trap_uniform x h with hall | hall
    · exact hj (hall j)
    · exact hall i hi

/-- The number of boundaries (neighbouring pairs that differ) round the ring. -/
def D (x : State (Fin (n + 1))) : Nat :=
  (List.finRange (n + 1)).countP (fun i => x i != x (nxt i))

/-- **The ring has no trap iff `0 < D x < n + 1`.** -/
theorem ring_noTrap_iff_count (x : State (Fin (n + 1))) :
    ¬ HasTrap E x ↔ 0 < D x ∧ D x < n + 1 := by
  rw [ring_noTrap_iff]
  have hlen : (List.finRange (n + 1)).length = n + 1 := List.length_finRange
  have hle : D x ≤ n + 1 := hlen ▸ List.countP_le_length
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    refine ⟨?_, ?_⟩
    · unfold D
      exact List.countP_pos_iff.mpr ⟨j, List.mem_finRange j, by simpa using hj⟩
    · apply Nat.lt_of_le_of_ne hle
      intro heq
      have := (List.countP_eq_length (l := List.finRange (n + 1))
        (p := fun i => x i != x (nxt i))).mp (by unfold D at heq; rw [heq, hlen])
      have := this i (List.mem_finRange i)
      simp [hi] at this
  · rintro ⟨hpos, hlt⟩
    refine ⟨?_, ?_⟩
    · apply Classical.byContradiction
      intro hne
      apply Nat.lt_irrefl (n + 1)
      have hall : D x = n + 1 := by
        have h2 : (List.finRange (n + 1)).countP (fun i => x i != x (nxt i)) =
            (List.finRange (n + 1)).length := by
          apply List.countP_eq_length.mpr
          intro i _
          have : x i ≠ x (nxt i) := fun h => hne ⟨i, h⟩
          simpa using this
        unfold D; rw [h2]; exact hlen
      omega
    · obtain ⟨j, _, hj⟩ := List.countP_pos_iff.mp hpos
      exact ⟨j, by simpa using hj⟩

/-- **Research's floor for a ring, exactly:** a ring of `S = n + 1` stages holding `T` tokens
(`D x = 2 T`) has no trap iff `1 ≤ T` and `S ≥ 2T + 1`. -/
theorem ring_live_tokens (x : State (Fin (n + 1))) (T : Nat) (hT : D x = 2 * T) :
    ¬ HasTrap E x ↔ 1 ≤ T ∧ 2 * T + 1 ≤ n + 1 := by
  rw [ring_noTrap_iff_count, hT]
  omega

/-- Sanity: a 3-stage ring with one token (`D = 2`) is live; a 2-stage ring with one token is not. -/
example : ¬ HasTrap (E (n := 2)) (fun i : Fin 3 => decide (i.val = 0)) := by
  rw [ring_noTrap_iff]
  exact ⟨⟨⟨1, by omega⟩, by decide⟩, ⟨⟨0, by omega⟩, by decide⟩⟩

example : HasTrap (E (n := 1)) (fun i : Fin 2 => decide (i.val = 0)) := by
  apply Classical.byContradiction
  intro h
  obtain ⟨⟨i, hi⟩, _⟩ := (ring_noTrap_iff _).mp h
  revert hi
  revert i
  decide

end Formal.Net.StageNet.RingLive
