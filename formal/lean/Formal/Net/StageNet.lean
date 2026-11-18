/-!
# Liveness of a stage network: never deadlocks iff no zero-token trap (shard C, 2026-11-18)

**Problem, plainly.** research's suite found kernels that bdc compiles into circuits that
deadlock (quadrec: a ring holding as many tokens as it has room for; nested / nest3 / lfsrfind:
an inner loop with zero trips). Research derived a condition ("token floor",
`research/data/suite/ringfloor.md`) and put it into bdc. This file proves, for the stage-level
model that derivation uses, the exact condition under which such a network can deadlock.

**Model (the stage network).** A finite set of storage stages `V` (Muller half buffers: a
`bd_link` controller is one, a `bd_pipe N` is N) and a relation `E p t`: stage `p` feeds stage
`t` through combinational rendezvous cells only (joins, forks, a mux's select join, a steer
routed one way). Each stage holds one bit `x t`. Stage `t` is *excited* when every stage
feeding it differs from it and every stage it feeds equals it; firing flips its bit; one stage
fires at a time, in any order (speed independence). For a single predecessor `a` and successor
`b` this is exactly the `bd_link` controller `c = C(a, ¬b)` (`excited_single`, against
`Ring.ctl`, whose agreement with the real LUT's run mode is `Ring.c2n_run`). Joins and forks of several stages are a
C-element on the requests / acknowledges: that they add no state of their own beyond these
arcs is the named modelling hypothesis **H_RENDEZVOUS** (not proved here; checked on the cell
models by `formal/tools/live/cells/`). The mode is fixed: every mux / merge / steer routes
one way (a loop iterating, say), as in research's derivation.

**The zero graph.** For a state `x`, `Z x a b` is the arc `a → b` of the marked graph that
holds no token: `a` feeds `b` and they agree, or `b` feeds `a` and they differ. A *trap* is
a nonempty set of stages each of which has a `Z`-predecessor inside the set (in a finite
network this is the same as a cycle of token-free arcs: follow predecessors until one repeats;
not formalised here). In research's terms a
trap is a closed walk, forward along some channels and backward along others, holding no token.

**Proved (no hypotheses beyond the model):**
* `excited_iff_noZ`: a stage is excited iff no zero arc enters it.
* `trap_step_iff`: one firing neither creates nor destroys a trap (`HasTrap` is invariant).
* `trap_dead`: every stage of a trap is never excited again, in any reachable state.
* `deadlock_trap`: a state with no excited stage (and some stage) is a trap (the whole set).
* `deadlock_free`: **from a trap-free state no reachable state is a deadlock.** With
  `trap_dead`, a trap is exactly what makes some stage dead forever.
* `fair_all_fire`: in any infinite weakly fair run from a trap-free state, EVERY stage fires
  infinitely often (stronger than deadlock freedom: no part of the network starves).

**Not covered:** the mode changes (a loop being entered or left, an inner loop passed through
in one trip); H_RENDEZVOUS (C-element joins / forks / mux select joins as pure arcs); data,
timing and glitches (this is the speed-independent control skeleton); the arbitrated merge.
That the graph bdc emits is the graph checked is the exporter's job
(`formal/tools/live/fixtures/`), untrusted.
-/

namespace Formal.Net.StageNet

variable {V : Type}

/-- A stage state: one bit per storage stage (the link controller's `c`). -/
abbrev State (V : Type) := V → Bool

/-- Stage `t` may fire: every stage feeding it differs from it, every stage it feeds equals it. -/
def Excited (E : V → V → Prop) (x : State V) (t : V) : Prop :=
  (∀ p, E p t → x p ≠ x t) ∧ (∀ q, E t q → x q = x t)

/-- Flip stage `t`. -/
def fire [DecidableEq V] (x : State V) (t : V) : State V :=
  fun v => if v = t then !x t else x v

/-- One speed-independent step: an excited stage fires. -/
inductive Step [DecidableEq V] (E : V → V → Prop) : State V → State V → Prop
  | mk {x : State V} {t : V} : Excited E x t → Step E x (fire x t)

/-- Reachability by steps. -/
inductive Reach [DecidableEq V] (E : V → V → Prop) : State V → State V → Prop
  | refl (x : State V) : Reach E x x
  | tail {x y z : State V} : Reach E x y → Step E y z → Reach E x z

/-- The token-free arc `a → b` of the marked graph in state `x`. -/
def Z (E : V → V → Prop) (x : State V) (a b : V) : Prop :=
  (E a b ∧ x a = x b) ∨ (E b a ∧ x b ≠ x a)

/-- A trap: a nonempty set of stages, each with a token-free arc into it from the set. -/
def Trap (E : V → V → Prop) (x : State V) (S : V → Prop) : Prop :=
  (∃ v, S v) ∧ ∀ u, S u → ∃ a, S a ∧ Z E x a u

def HasTrap (E : V → V → Prop) (x : State V) : Prop := ∃ S, Trap E x S

theorem excited_iff_noZ (E : V → V → Prop) (x : State V) (t : V) :
    Excited E x t ↔ ∀ a, ¬ Z E x a t := by
  unfold Excited Z
  constructor
  · rintro ⟨h1, h2⟩ a (⟨he, hx⟩ | ⟨he, hx⟩)
    · exact h1 a he hx
    · exact hx (h2 a he).symm
  · intro h
    refine ⟨fun p hp hx => h p (Or.inl ⟨hp, hx⟩), fun q hq => ?_⟩
    cases hxq : x q <;> cases hxt : x t <;> simp_all

theorem fire_self [DecidableEq V] (x : State V) (t : V) : fire x t t = !x t := by
  simp [fire]

theorem fire_ne [DecidableEq V] (x : State V) {t v : V} (h : v ≠ t) : fire x t v = x v := by
  simp [fire, h]

/-- Arcs not touching the fired stage are unchanged. -/
theorem Z_fire_ne [DecidableEq V] (E : V → V → Prop) (x : State V) {t a b : V}
    (ha : a ≠ t) (hb : b ≠ t) : Z E (fire x t) a b ↔ Z E x a b := by
  simp [Z, fire_ne x ha, fire_ne x hb]

/-- After `t` fires, an arc out of `t` is token-free iff the reverse arc was before. -/
theorem Z_fire_out [DecidableEq V] (E : V → V → Prop) (x : State V) {t u : V} (hu : u ≠ t) :
    Z E (fire x t) t u ↔ Z E x u t := by
  unfold Z
  rw [fire_self, fire_ne x hu]
  cases hxt : x t <;> cases hxu : x u <;> simp

/-- After an excited stage fires, no token-free arc leaves it. -/
theorem no_Z_out_after [DecidableEq V] (E : V → V → Prop) (x : State V) {t : V}
    (he : Excited E x t) (u : V) : ¬ Z E (fire x t) t u := by
  intro h
  by_cases hu : u = t
  · subst hu
    have hE : E u u := by rcases h with ⟨h', _⟩ | ⟨h', _⟩ <;> exact h'
    exact (excited_iff_noZ E x u).1 he u (Or.inl ⟨hE, rfl⟩)
  · exact (excited_iff_noZ E x t).1 he u ((Z_fire_out E x hu).1 h)

/-- A trap survives any firing (the fired stage is not in it). -/
theorem trap_fire_fwd [DecidableEq V] (E : V → V → Prop) (x : State V) {t : V}
    (he : Excited E x t) {S : V → Prop} (hS : Trap E x S) : Trap E (fire x t) S := by
  have hnt : ¬ S t := by
    intro ht
    obtain ⟨a, _, ha⟩ := hS.2 t ht
    exact (excited_iff_noZ E x t).1 he a ha
  refine ⟨hS.1, fun u hu => ?_⟩
  obtain ⟨a, haS, ha⟩ := hS.2 u hu
  have hut : u ≠ t := fun h => hnt (h ▸ hu)
  have hat : a ≠ t := fun h => hnt (h ▸ haS)
  exact ⟨a, haS, (Z_fire_ne E x hat hut).2 ha⟩

/-- A trap after a firing was a trap (possibly without the fired stage) before. -/
theorem trap_fire_bwd [DecidableEq V] (E : V → V → Prop) (x : State V) {t : V}
    (he : Excited E x t) {S : V → Prop} (hS : Trap E (fire x t) S) :
    Trap E x (fun v => S v ∧ v ≠ t) := by
  -- in `fire x t`, nothing has a token-free arc from `t`
  have hpred : ∀ u, S u → ∃ a, S a ∧ a ≠ t ∧ Z E (fire x t) a u := by
    intro u hu
    obtain ⟨a, haS, ha⟩ := hS.2 u hu
    refine ⟨a, haS, fun hat => ?_, ha⟩
    subst hat
    exact no_Z_out_after E x he u ha
  obtain ⟨v, hv⟩ := hS.1
  refine ⟨?_, fun u ⟨hu, hut⟩ => ?_⟩
  · obtain ⟨a, haS, hat, _⟩ := hpred v hv
    exact ⟨a, haS, hat⟩
  · obtain ⟨a, haS, hat, ha⟩ := hpred u hu
    exact ⟨a, ⟨haS, hat⟩, (Z_fire_ne E x hat hut).1 ha⟩

theorem trap_step_iff [DecidableEq V] (E : V → V → Prop) {x y : State V} (h : Step E x y) :
    HasTrap E x ↔ HasTrap E y := by
  cases h with
  | mk he => exact ⟨fun ⟨S, hS⟩ => ⟨S, trap_fire_fwd E _ he hS⟩,
                    fun ⟨S, hS⟩ => ⟨_, trap_fire_bwd E _ he hS⟩⟩

theorem trap_reach_iff [DecidableEq V] (E : V → V → Prop) {x y : State V} (h : Reach E x y) :
    HasTrap E x ↔ HasTrap E y := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hs ih => exact ih.trans (trap_step_iff E hs)

/-- A trap is forever: in every reachable state the same set is a trap. -/
theorem trap_reach [DecidableEq V] (E : V → V → Prop) {x y : State V} (h : Reach E x y)
    {S : V → Prop} (hS : Trap E x S) : Trap E y S := by
  induction h with
  | refl => exact hS
  | tail _ hs ih => cases hs with | mk he => exact trap_fire_fwd E _ he ih

/-- Every stage of a trap is dead: never excited in any reachable state. -/
theorem trap_dead [DecidableEq V] (E : V → V → Prop) {x y : State V} (h : Reach E x y)
    {S : V → Prop} (hS : Trap E x S) {u : V} (hu : S u) : ¬ Excited E y u := by
  intro he
  obtain ⟨a, _, ha⟩ := (trap_reach E h hS).2 u hu
  exact (excited_iff_noZ E y u).1 he a ha

/-- A deadlock (no stage excited) is a trap: the whole stage set. -/
theorem deadlock_trap (E : V → V → Prop) (x : State V) (hne : Nonempty V)
    (hd : ∀ t, ¬ Excited E x t) : Trap E x (fun _ => True) := by
  obtain ⟨v0⟩ := hne
  refine ⟨⟨v0, trivial⟩, fun u _ => ?_⟩
  have := hd u
  rw [excited_iff_noZ] at this
  obtain ⟨a, ha⟩ := Classical.not_forall.mp this
  exact ⟨a, trivial, Classical.not_not.mp ha⟩

/-- **No trap, no deadlock.** From a trap-free state no reachable state is a deadlock. -/
theorem deadlock_free [DecidableEq V] (E : V → V → Prop) (hne : Nonempty V) {x : State V}
    (hn : ¬ HasTrap E x) {y : State V} (hy : Reach E x y) : ∃ t, Excited E y t := by
  refine Classical.byContradiction fun hd => ?_
  exact hn ((trap_reach_iff E hy).2 ⟨_, deadlock_trap E y hne (fun t ht => hd ⟨t, ht⟩)⟩)

/-! ## Fair runs: every stage fires infinitely often -/

/-- An infinite execution: every step fires an excited stage. -/
def IsRun [DecidableEq V] (E : V → V → Prop) (r : Nat → State V) : Prop := ∀ n, Step E (r n) (r (n + 1))

/-- Stage `v` fires at step `m`. -/
def Fires (r : Nat → State V) (v : V) (m : Nat) : Prop := r (m + 1) v ≠ r m v

/-- Weak fairness: a stage excited at `n` fires at some step `m ≥ n` (H_CEL_FAIR). -/
def Fair (E : V → V → Prop) (r : Nat → State V) : Prop :=
  ∀ n t, Excited E (r n) t → ∃ m, n ≤ m ∧ Fires r t m

theorem run_reach [DecidableEq V] {E : V → V → Prop} {r : Nat → State V} (hr : IsRun E r) :
    ∀ n, Reach E (r 0) (r n)
  | 0 => Reach.refl _
  | n + 1 => Reach.tail (run_reach hr n) (hr n)

theorem step_fire [DecidableEq V] {E : V → V → Prop} {x y : State V} (h : Step E x y) :
    ∃ c, Excited E x c ∧ y = fire x c := by
  cases h with | mk he => exact ⟨_, he, rfl⟩

/-- Once `a` has fired, the arc `a → v` keeps a token until `v` fires. -/
theorem arc_marked_until [DecidableEq V] {E : V → V → Prop} {r : Nat → State V} (hr : IsRun E r)
    {a v : V} (hav : a ≠ v) {m : Nat} (hm : Fires r a m) :
    ∀ k, (∀ j, m < j → j < m + 1 + k → ¬ Fires r v j) → ¬ Z E (r (m + 1 + k)) a v := by
  intro k
  induction k with
  | zero =>
    intro _
    obtain ⟨c, hc, hy⟩ := step_fire (hr m)
    have hca : c = a := by
      refine Classical.byContradiction fun hca => ?_
      apply hm
      rw [hy, fire_ne _ (Ne.symm hca)]
    subst hca
    simpa [hy] using no_Z_out_after E (r m) hc v
  | succ k ih =>
    intro hnv
    have ih' := ih (fun j h1 h2 => hnv j h1 (by omega))
    obtain ⟨c, hc, hy⟩ := step_fire (hr (m + 1 + k))
    have hy' : r (m + 1 + (k + 1)) = fire (r (m + 1 + k)) c := by
      rw [show m + 1 + (k + 1) = m + 1 + k + 1 by omega]; exact hy
    rw [hy']
    by_cases hcv : c = v
    · subst hcv
      exfalso
      apply hnv (m + 1 + k) (by omega) (by omega)
      show r (m + 1 + k + 1) c ≠ r (m + 1 + k) c
      rw [hy, fire_self]; cases r (m + 1 + k) c <;> simp
    by_cases hca : c = a
    · subst hca; exact no_Z_out_after E _ hc v
    · rw [Z_fire_ne E _ (Ne.symm hca) (Ne.symm hcv)]; exact ih'

/-- The largest value of `f` on a list. -/
def maxOn (f : V → Nat) : List V → Nat
  | [] => 0
  | v :: l => max (f v) (maxOn f l)

theorem le_maxOn (f : V → Nat) : ∀ {l : List V} {v : V}, v ∈ l → f v ≤ maxOn f l
  | _ :: _, _, List.Mem.head _ => Nat.le_max_left _ _
  | _ :: _, _, List.Mem.tail _ h => Nat.le_trans (le_maxOn f h) (Nat.le_max_right _ _)

open Classical in
/-- **Every stage fires infinitely often** in a weakly fair infinite run from a trap-free state.
`nodes` lists every stage (the network is finite). -/
theorem fair_all_fire [DecidableEq V] (E : V → V → Prop) (nodes : List V)
    (hnodes : ∀ v, v ∈ nodes) {r : Nat → State V}
    (hr : IsRun E r) (hf : Fair E r) (hn : ¬ HasTrap E (r 0)) :
    ∀ v N, ∃ m, N ≤ m ∧ Fires r v m := by
  refine Classical.byContradiction fun hc => ?_
  obtain ⟨u, hu⟩ := Classical.not_forall.mp hc
  obtain ⟨Nu, hu⟩ := Classical.not_forall.mp hu
  have hu : ∀ m, Nu ≤ m → ¬ Fires r u m := fun m hm hfm => hu ⟨m, hm, hfm⟩
  -- S: the stages that eventually stop firing
  let S : V → Prop := fun v => ∃ N, ∀ m, N ≤ m → ¬ Fires r v m
  have hgex : ∀ v, ∃ N, S v → ∀ m, N ≤ m → ¬ Fires r v m := fun v =>
    if hv : S v then (let ⟨N, hN⟩ := hv; ⟨N, fun _ => hN⟩) else ⟨0, fun h => absurd h hv⟩
  let g : V → Nat := fun v => Classical.choose (hgex v)
  have hg : ∀ v, S v → ∀ m, g v ≤ m → ¬ Fires r v m := fun v => Classical.choose_spec (hgex v)
  let N0 := maxOn g nodes
  have hS : ∀ v, S v → ∀ m, N0 ≤ m → ¬ Fires r v m :=
    fun v hv m hm => hg v hv m (Nat.le_trans (le_maxOn g (hnodes v)) hm)
  -- a later time by which every stage outside S has fired again
  have hhex : ∀ v, ∃ M, ¬ S v → N0 ≤ M ∧ Fires r v M := fun v => by
    by_cases hv : S v
    · exact ⟨0, fun h => absurd hv h⟩
    · have : ∃ m, N0 ≤ m ∧ Fires r v m := by
        refine Classical.byContradiction fun hc => hv ⟨N0, fun m hm hfm => hc ⟨m, hm, hfm⟩⟩
      obtain ⟨m, hm, hfm⟩ := this
      exact ⟨m, fun _ => ⟨hm, hfm⟩⟩
  let h : V → Nat := fun v => Classical.choose (hhex v)
  have hh : ∀ v, ¬ S v → N0 ≤ h v ∧ Fires r v (h v) := fun v => Classical.choose_spec (hhex v)
  let T := max N0 (maxOn h nodes) + 1
  -- S is a trap at time T
  have htrap : Trap E (r T) S := by
    refine ⟨⟨u, Nu, hu⟩, fun v hv => ?_⟩
    have hne : ¬ Excited E (r T) v := by
      intro he
      obtain ⟨m, hm, hfm⟩ := hf T v he
      exact hS v hv m (Nat.le_trans (by omega) hm) hfm
    rw [excited_iff_noZ] at hne
    obtain ⟨a, ha⟩ := Classical.not_forall.mp hne
    have ha := Classical.not_not.mp ha
    refine ⟨a, ?_, ha⟩
    refine Classical.byContradiction fun haS => ?_
    have hav : a ≠ v := fun he => haS (he ▸ hv)
    obtain ⟨_, hfm⟩ := hh a haS
    have hmT : h a + 1 ≤ T := by
      have := le_maxOn h (hnodes a); omega
    have hk := arc_marked_until hr hav hfm (T - (h a + 1))
      (fun j h1 _ => hS v hv j (by have := (hh a haS).1; omega))
    rw [show h a + 1 + (T - (h a + 1)) = T by omega] at hk
    exact hk ha
  exact hn ((trap_reach_iff E (run_reach hr T)).2 ⟨S, htrap⟩)

end Formal.Net.StageNet
