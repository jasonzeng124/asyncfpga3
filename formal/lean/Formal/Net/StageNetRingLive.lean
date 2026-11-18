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
* `ring_live_rest` (with `D_rest`, `countP_nxt`): at research's rest marking (values resting in
  non-adjacent stages) `D = 2T`, so the ring has no trap iff `T ≥ 1` and `S ≥ 2T + 1`, with no
  hypothesis left.
* `cycle_noTrap_iff`: the same for a cycle whose channels point either way round (a fork-join
  pair: P forward, Q backward): no trap iff its token-free arcs do not all point one way.
* `cycle_noTrap_iff_count`: with F / B channels pointing forward / back round the cycle, dF / dB
  of them joining stages that differ: no trap iff `dF < F + dB` and `dB < B + dF`; at a rest
  marking (d = 2 x tokens) this is research's condition 1 for rings and condition 2
  (`L_Q ≥ 2K`, and the same with P and Q exchanged) for fork-join pairs.
* `hasTrap_mono`: a trap of a sub-network is a trap of any network containing it, so a trapped
  ring or fork-join pair inside a kernel kills its stages there (`trap_dead`).
With `StageNet.deadlock_free` / `fair_all_fire`, "no trap" means: no reachable deadlock and every
stage fires infinitely often in weakly fair runs; with `trap_dead`, a trap means some stage
(here: every stage of the trap) is dead forever.

**Scope.** The iff statements are about a network that IS the cycle. For a ring or fork-join pair
inside a kernel the conditions are necessary (`hasTrap_mono`); that they are also sufficient
needs them on every cycle of the kernel's stage graph (`StageNet.cycle_of_trap`: a trap contains
a token-free closed walk), which is what research's walk view and formal's certificates check.

**Not covered:** everything `StageNet` leaves out (H_RENDEZVOUS, mode changes, timing, data).
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

/-! ## Any cycle of stages, channels oriented either way (fork-join pairs included)

A fork-join pair (research's condition 2) is a cycle of stages whose channels do not all point
the same way round: from the fork along path P to the join, and back from the join along path
Q against its channels. `o i` says how the channel between stage `i` and `nxt i` points
(`true`: `i` feeds `nxt i`). The token-free arc of that channel points *clockwise* (from `i` to
`nxt i`) iff the two stages agree and the channel points clockwise, or they differ and it points
back (`cw`). A cycle is trapped iff all its token-free arcs point the same way round. -/

/-- The channels of an oriented cycle. -/
def EO (o : Fin (n + 1) → Bool) (a b : Fin (n + 1)) : Prop :=
  (b = nxt a ∧ o a = true) ∨ (a = nxt b ∧ o b = false)

/-- The token-free arc of channel `i` points from `i` to `nxt i`. -/
def cw (o : Fin (n + 1) → Bool) (x : State (Fin (n + 1))) (i : Fin (n + 1)) : Prop :=
  (o i = true ∧ x i = x (nxt i)) ∨ (o i = false ∧ x i ≠ x (nxt i))

theorem into_o (o : Fin (n + 1) → Bool) (x : State (Fin (n + 1))) (a v : Fin (n + 1))
    (hz : Z (EO o) x a v) :
    (a = prv v ∧ cw o x (prv v)) ∨ (a = nxt v ∧ ¬ cw o x v) := by
  unfold cw
  rcases hz with ⟨⟨hv, ho⟩ | ⟨ha, ho⟩, hx⟩ | ⟨⟨ha, ho⟩ | ⟨hv, ho⟩, hx⟩
  · left; subst hv; rw [prv_nxt]; exact ⟨rfl, Or.inl ⟨ho, hx⟩⟩
  · right; subst ha; refine ⟨rfl, ?_⟩
    rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · rw [ho] at h1; exact Bool.noConfusion h1
    · exact h2 hx.symm
  · right; subst ha; refine ⟨rfl, ?_⟩
    rintro (⟨_, h2⟩ | ⟨h1, _⟩)
    · exact hx h2
    · rw [ho] at h1; exact Bool.noConfusion h1
  · left; subst hv; rw [prv_nxt]; refine ⟨rfl, Or.inr ⟨ho, fun h => hx h.symm⟩⟩

/-- A trap of an oriented cycle forces every token-free arc to point the same way round. -/
theorem trap_uniform_o (o : Fin (n + 1) → Bool) (x : State (Fin (n + 1)))
    (h : HasTrap (EO o) x) : (∀ i, cw o x i) ∨ (∀ i, ¬ cw o x i) := by
  obtain ⟨S, ⟨u, hu⟩, hS⟩ := h
  obtain ⟨a, ha, hz⟩ := hS u hu
  rcases into_o o x a u hz with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · left
    have step : ∀ v, (S v ∧ cw o x v) → (S (prv v) ∧ cw o x (prv v)) := by
      rintro v ⟨hv, hvx⟩
      obtain ⟨b, hb, hzb⟩ := hS v hv
      rcases into_o o x b v hzb with ⟨rfl, hbx⟩ | ⟨rfl, hbx⟩
      · exact ⟨hb, hbx⟩
      · exact absurd hvx hbx
    exact fun i => (ind_prv (fun v => S v ∧ cw o x v) step (prv u) ⟨ha, hx⟩ i).2
  · right
    have step : ∀ w, (S w ∧ ¬ cw o x (prv w)) → (S (nxt w) ∧ ¬ cw o x (prv (nxt w))) := by
      rintro w ⟨hw, hwx⟩
      obtain ⟨b, hb, hzb⟩ := hS w hw
      rcases into_o o x b w hzb with ⟨rfl, hbx⟩ | ⟨rfl, hbx⟩
      · exact absurd hbx hwx
      · exact ⟨hb, by rw [prv_nxt]; exact hbx⟩
    have all := ind_nxt (fun w => S w ∧ ¬ cw o x (prv w)) step (nxt u) ⟨ha, by rw [prv_nxt]; exact hx⟩
    intro i
    have := (all (nxt i)).2
    rwa [prv_nxt] at this

/-- **An oriented cycle has no trap iff its token-free arcs do not all point the same way round.**
For `o` constant `true` this is `ring_noTrap_iff`. -/
theorem cycle_noTrap_iff (o : Fin (n + 1) → Bool) (x : State (Fin (n + 1))) :
    ¬ HasTrap (EO o) x ↔ (∃ i, cw o x i) ∧ (∃ j, ¬ cw o x j) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · -- every arc points back: each stage has a token-free arc in from its successor
      apply Classical.byContradiction
      intro hne
      apply h
      refine ⟨fun _ => True, ⟨⟨0, by omega⟩, trivial⟩, fun v _ => ⟨nxt v, trivial, ?_⟩⟩
      have hv : ¬ cw o x v := fun hc => hne ⟨v, hc⟩
      unfold cw at hv
      cases ho : o v
      · -- channel v points back (nxt v feeds v), stages agree: arc nxt v → v
        left
        refine ⟨Or.inr ⟨rfl, ho⟩, ?_⟩
        apply Classical.byContradiction
        intro hd
        exact hv (Or.inr ⟨ho, fun he => hd he.symm⟩)
      · -- channel v points forward (v feeds nxt v), stages differ: arc nxt v → v
        right
        refine ⟨Or.inl ⟨rfl, ho⟩, ?_⟩
        intro he
        exact hv (Or.inl ⟨ho, he⟩)
    · -- every arc points forward: each stage has a token-free arc in from its predecessor
      apply Classical.byContradiction
      intro hne
      apply h
      refine ⟨fun _ => True, ⟨⟨0, by omega⟩, trivial⟩, fun v _ => ⟨prv v, trivial, ?_⟩⟩
      have hc : cw o x (prv v) := Classical.byContradiction (fun hc => hne ⟨prv v, hc⟩)
      unfold cw at hc
      rcases hc with ⟨ho, hx⟩ | ⟨ho, hx⟩
      · left
        refine ⟨Or.inl ⟨(nxt_prv v).symm, ho⟩, ?_⟩
        rwa [nxt_prv] at hx
      · right
        refine ⟨Or.inr ⟨(nxt_prv v).symm, ho⟩, ?_⟩
        rw [nxt_prv] at hx
        exact fun he => hx he.symm
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ h
    rcases trap_uniform_o o x h with hall | hall
    · exact hj (hall j)
    · exact hall i hi

/-- Adding channels can only add traps: a trap of a sub-network is a trap of the network. So an
oriented cycle (a ring, a fork-join pair) whose token-free arcs all point one way, found inside
any network, is a trap there, and by `StageNet.trap_dead` its stages never fire again. -/
theorem hasTrap_mono {V : Type} {E E' : V → V → Prop} (hE : ∀ a b, E a b → E' a b)
    {x : State V} (h : HasTrap E x) : HasTrap E' x := by
  obtain ⟨S, hne, hS⟩ := h
  refine ⟨S, hne, fun u hu => ?_⟩
  obtain ⟨a, ha, hz⟩ := hS u hu
  refine ⟨a, ha, ?_⟩
  rcases hz with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact Or.inl ⟨hE _ _ he, hx⟩
  · exact Or.inr ⟨hE _ _ he, hx⟩

/-- Sanity, research's condition 2: a fork-join pair, fork 0, join 2, path P = 0 → 1 → 2, path
Q = 0 → 3 → 2 with ONE stage (3) holding a token more than P (stage 3 differs from the rest):
trapped (Q needs 2K = 2 stages). -/
example : HasTrap (EO (n := 3) (fun i => decide (i.val < 2))) (fun i => decide (i.val = 3)) := by
  apply Classical.byContradiction
  intro h
  obtain ⟨_, ⟨j, hj⟩⟩ := (cycle_noTrap_iff _ _).mp h
  revert hj; revert j; unfold cw nxt; decide

/-- ... and with TWO stages on Q (0 → 4 → 3 → 2), the first holding the token: no trap. -/
example : ¬ HasTrap (EO (n := 4) (fun i => decide (i.val < 2))) (fun i => decide (i.val = 4)) := by
  rw [cycle_noTrap_iff]
  refine ⟨⟨⟨0, by omega⟩, ?_⟩, ⟨⟨2, by omega⟩, ?_⟩⟩ <;> unfold cw nxt <;> decide

/-! ## Counting form for an oriented cycle: research's conditions 1 and 2 in one statement

With `F` channels pointing forward round the cycle (`o i = true`) and `B` pointing back, of which
`dF` and `dB` join two stages that differ, the cycle has no trap iff `dF < F + dB` and
`dB < B + dF`. At research's rest marking a value resting in a stage makes the two channels
around it differ, so `dF = 2 T_fwd`, `dB = 2 T_back`:
* a ring (`B = 0`, `F = S`): `0 < 2T < S`, i.e. `T ≥ 1` and `S ≥ 2T + 1` (condition 1);
* a fork-join pair, P forward (`F = L_P + 1` channels from the shared stage before the fork to
  the one after the join), Q backward (`B = L_Q + 1`): `2 T_Q < L_Q + 1 + 2 T_P`, i.e.
  `L_Q ≥ 2K` with `K = T_Q - T_P` (condition 2), and the same with P and Q exchanged. -/

/-- One element's bookkeeping, summed over a list. -/
theorem count_split (l : List (Fin (n + 1))) (a e : Fin (n + 1) → Bool) :
    l.countP (fun i => (a i && e i) || (!a i && !e i)) + l.countP (fun i => a i && !e i) =
      l.countP a + l.countP (fun i => !a i && !e i) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.countP_cons]
    cases a i <;> cases e i <;> simp <;> omega

theorem count_total (l : List (Fin (n + 1))) (a : Fin (n + 1) → Bool) :
    l.countP a + l.countP (fun i => !a i) = l.length := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.countP_cons, List.length_cons]
    cases a i <;> simp <;> omega

/-- **An oriented cycle has no trap iff `dF < F + dB` and `dB < B + dF`.** -/
theorem cycle_noTrap_iff_count (o : Fin (n + 1) → Bool) (x : State (Fin (n + 1))) :
    let L := List.finRange (n + 1)
    let F := L.countP o
    let B := L.countP (fun i => !o i)
    let dF := L.countP (fun i => o i && !(x i == x (nxt i)))
    let dB := L.countP (fun i => !o i && !(x i == x (nxt i)))
    ¬ HasTrap (EO o) x ↔ dF < F + dB ∧ dB < B + dF := by
  intro L F B dF dB
  rw [cycle_noTrap_iff]
  have hcw : ∀ i, cw o x i ↔ ((o i && (x i == x (nxt i))) || (!o i && !(x i == x (nxt i)))) = true := by
    intro i; unfold cw; cases o i <;> cases x i <;> cases x (nxt i) <;> simp
  let C := L.countP (fun i => (o i && (x i == x (nxt i))) || (!o i && !(x i == x (nxt i))))
  have hsplit : C + dF = F + dB := count_split L o (fun i => x i == x (nxt i))
  have htot : F + B = n + 1 := by
    have := count_total L o; rw [List.length_finRange] at this; exact this
  have hle : C ≤ n + 1 := by
    have := List.countP_le_length (l := L)
      (p := fun i => (o i && (x i == x (nxt i))) || (!o i && !(x i == x (nxt i))))
    rwa [List.length_finRange] at this
  have hpos : (∃ i, cw o x i) ↔ 0 < C := by
    constructor
    · rintro ⟨i, hi⟩
      exact List.countP_pos_iff.mpr ⟨i, List.mem_finRange i, (hcw i).mp hi⟩
    · intro h
      obtain ⟨i, _, hi⟩ := List.countP_pos_iff.mp h
      exact ⟨i, (hcw i).mpr hi⟩
  have hfull : (∃ j, ¬ cw o x j) ↔ C < n + 1 := by
    constructor
    · rintro ⟨j, hj⟩
      apply Nat.lt_of_le_of_ne hle
      intro heq
      have hall := (List.countP_eq_length (l := L)
        (p := fun i => (o i && (x i == x (nxt i))) || (!o i && !(x i == x (nxt i))))).mp
        (by show C = L.length; rw [heq, List.length_finRange])
      exact hj ((hcw j).mpr (hall j (List.mem_finRange j)))
    · intro h
      apply Classical.byContradiction
      intro hne
      have hall : C = L.length := by
        apply List.countP_eq_length.mpr
        intro i _
        exact (hcw i).mp (Classical.byContradiction (fun hc => hne ⟨i, hc⟩))
      rw [List.length_finRange] at hall
      omega
  rw [hpos, hfull]
  omega

/-! ## Research's rest marking gives `D = 2T`

At an iteration boundary research reads the ring with each loop-carried value resting in one
stage (that stage high, its neighbours low). With no two resting stages adjacent, the number of
differing neighbouring pairs is twice the number of resting values, so `ring_live_tokens`
applies with `T` = the number of resting values. -/

/-- Counting round the ring is invariant under the rotation `nxt`. -/
theorem countP_nxt (p : Fin (n + 1) → Bool) :
    (List.finRange (n + 1)).countP (fun i => p (nxt i)) = (List.finRange (n + 1)).countP p := by
  conv => lhs; rw [List.finRange_succ_last]
  conv => rhs; rw [List.finRange_succ]
  simp only [List.countP_append, List.countP_map, List.countP_cons, List.countP_nil]
  have h1 : (List.finRange n).countP ((fun i => p (nxt i)) ∘ Fin.castSucc) =
      (List.finRange n).countP (p ∘ Fin.succ) := by
    congr 1; funext i
    have : nxt (Fin.castSucc i) = Fin.succ i := by
      have hne : ¬ ((Fin.castSucc i).val + 1 = n + 1) := by
        have := i.isLt; simp only [Fin.val_castSucc]; omega
      apply Fin.ext; unfold nxt; rw [dif_neg hne]; simp
    simp [this]
  have h2 : nxt (Fin.last n) = (0 : Fin (n + 1)) := by
    apply Fin.ext; unfold nxt; simp
  rw [h1, h2]
  cases p 0 <;> simp <;> omega

/-- Sum a per-element identity `[q i] = [a i] + [b i]` over a list. -/
theorem countP_sum (l : List (Fin (n + 1))) (q a b : Fin (n + 1) → Bool)
    (h : ∀ i, (if q i then 1 else 0) = (if a i then 1 else 0) + (if b i then 1 else 0)) :
    l.countP q = l.countP a + l.countP b := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.countP_cons]
    have := h i
    cases hq : q i <;> cases ha : a i <;> cases hb : b i <;> simp only [hq, ha, hb] at this ⊢ <;>
      simp at this ⊢ <;> omega

/-- At a rest marking (no two adjacent stages both hold a value), `D = 2T`. -/
theorem D_rest (x : State (Fin (n + 1))) (hR : ∀ i, x i = true → x (nxt i) = false) :
    D x = 2 * (List.finRange (n + 1)).countP x := by
  unfold D
  rw [countP_sum (List.finRange (n + 1)) (fun i => x i != x (nxt i)) x (fun i => x (nxt i)), countP_nxt]
  · omega
  · intro i
    have := hR i
    cases hx : x i <;> cases hy : x (nxt i) <;> simp_all

/-- **Research's floor for a ring at its rest marking:** a ring of `S = n + 1` stages with `T`
values resting in non-adjacent stages has no trap iff `T ≥ 1` and `S ≥ 2T + 1`. -/
theorem ring_live_rest (x : State (Fin (n + 1))) (hR : ∀ i, x i = true → x (nxt i) = false) :
    ¬ HasTrap E x ↔ 1 ≤ (List.finRange (n + 1)).countP x ∧
      2 * (List.finRange (n + 1)).countP x + 1 ≤ n + 1 :=
  ring_live_tokens x _ (D_rest x hR)

end Formal.Net.StageNet.RingLive
