import Formal.Net.StageNet

/-!
# H_RENDEZVOUS for C-element joins and forks: the gate network refines the stage network (shard C, 2026-11-18)

**Problem, plainly.** `StageNet` treats joins and forks as pure arcs between storage stages
(research's derivation: "they add arcs, not tokens"). In the circuit each stage `t` is a
`bd_link` controller `c_t = C(J_t, ¬K_t)` whose request input `J_t` is a C-element over the
requests `c_p` of the stages feeding it (a join, a compute op's operand join, a mux's select
join with the routing fixed) and whose acknowledge input `K_t` is a C-element over the stages
it feeds (a fork's acknowledge). Those C-elements hold state of their own. This file proves
that, for one level of C-elements per join and fork, they add no deadlock: the gate network's
deadlocks are exactly stage-network deadlocks.

**Gate model.** State: `c t` (stage), `J t` (its join), `K t` (its fork). Speed independent, one
gate at a time:
* stage `t` fires when `J t ≠ c t` and `K t = c t` (`C(J, ¬K)` excited), flipping `c t`;
* join `t` fires when every `c p` (`E p t`) differs from `J t`, flipping `J t`;
* fork `t` fires when every `c q` (`E t q`) differs from `K t`, flipping `K t`.
A stage with one feeder is the same with a one-input C-element (a buffer) in between, which
adds a gate delay and nothing else.

**Invariant `Inv`** (holds at the all-zero reset, `inv_zero`, and is preserved, `inv_step`):
for every stage `t`, `J t = c t` or every feeder of `t` equals `J t`; and if `K t = c t` then
every stage `t` feeds equals `c t`.

**Proved:**
* `proj_step`: under `Inv`, a gate step leaves the stage bits unchanged (join / fork) or is a
  `StageNet.Step` (a stage fires only when the stage rule allows it).
* `gate_dead_stage_dead`: under `Inv`, a gate state with no excited gate projects to a stage
  state with no excited stage.
* `gate_deadlock_free`: from a gate state with `Inv` whose stage bits have no trap, no
  reachable gate state is a deadlock.

**Not covered:** C-element TREES (`bd_ctree`, joins of more than four inputs: two levels of
C-elements; not modelled here), the mode changes, the arbiter, the steer's AND gates and the
mux select's AND (with the routing fixed they are a wire or a constant), timing, glitches and
Kleene X (the gates are binary and speed independent; H_SI as in `Ring.lean`).
-/

namespace Formal.Net.StageNet

variable {V : Type} [DecidableEq V]

/-- Gate-level state: stage controllers, their join C-elements, their fork C-elements. -/
structure GState (V : Type) where
  c : State V
  J : State V
  K : State V

/-- One speed-independent gate step. -/
inductive GStep (E : V → V → Prop) : GState V → GState V → Prop
  | stage {g : GState V} {t : V} : g.J t ≠ g.c t → g.K t = g.c t →
      GStep E g ⟨fire g.c t, g.J, g.K⟩
  | join {g : GState V} {t : V} : (∀ p, E p t → g.c p ≠ g.J t) →
      GStep E g ⟨g.c, fire g.J t, g.K⟩
  | fork {g : GState V} {t : V} : (∀ q, E t q → g.c q ≠ g.K t) →
      GStep E g ⟨g.c, g.J, fire g.K t⟩

inductive GReach (E : V → V → Prop) : GState V → GState V → Prop
  | refl (g : GState V) : GReach E g g
  | tail {g h k : GState V} : GReach E g h → GStep E h k → GReach E g k

/-- Some gate is excited. -/
def GLive (E : V → V → Prop) (g : GState V) : Prop :=
  ∃ t, (g.J t ≠ g.c t ∧ g.K t = g.c t) ∨ (∀ p, E p t → g.c p ≠ g.J t) ∨
    (∀ q, E t q → g.c q ≠ g.K t)

def Inv (E : V → V → Prop) (g : GState V) : Prop :=
  ∀ t, (g.J t = g.c t ∨ ∀ p, E p t → g.c p = g.J t) ∧
       (g.K t = g.c t → ∀ q, E t q → g.c q = g.c t)

omit [DecidableEq V] in
theorem inv_zero (E : V → V → Prop) : Inv E ⟨fun _ => false, fun _ => false, fun _ => false⟩ :=
  fun _ => ⟨Or.inl rfl, fun _ _ _ => rfl⟩

theorem bool_ne_iff {a b : Bool} : a ≠ b ↔ a = !b := by cases a <;> cases b <;> simp

theorem fire_eq_self_iff (f : State V) (t v : V) : fire f t v = f v ↔ v ≠ t := by
  by_cases h : v = t
  · subst h; simp [fire]
  · simp [fire, h]

theorem inv_step (E : V → V → Prop) {g h : GState V} (hi : Inv E g) (hs : GStep E g h) :
    Inv E h := by
  cases hs with
  | @stage t hJ hK =>
    -- feeders of `t` equal `J t`, consumers of `t` equal `c t`
    have hP : ∀ p, E p t → g.c p = g.J t := fun p hp =>
      ((hi t).1.resolve_left hJ) p hp
    have hQ : ∀ q, E t q → g.c q = g.c t := (hi t).2 hK
    intro u
    by_cases hut : u = t
    · subst hut
      refine ⟨Or.inl ?_, fun hK' => ?_⟩
      · simp only [fire, ↓reduceIte]; exact bool_ne_iff.mp hJ
      · exfalso; simp only [fire, ↓reduceIte] at hK'; rw [hK] at hK'
        cases h0 : g.c u <;> simp [h0] at hK'
    · have hcu : fire g.c t u = g.c u := by simp [fire, hut]
      refine ⟨?_, fun hK' q hq => ?_⟩
      · by_cases hJu : g.J u = g.c u
        · exact Or.inl (by simp only [hcu]; exact hJu)
        · right
          intro p hp
          have hpu := ((hi u).1.resolve_left hJu) p hp
          by_cases hpt : p = t
          · subst hpt
            -- `t` feeds `u`: `c u = c t = J u`, against `J u ≠ c u`
            exact absurd ((hQ u hp).trans hpu).symm hJu
          · simp [fire, hpt]; exact hpu
      · simp only [hcu] at hK' ⊢
        have hqu := (hi u).2 hK' q hq
        by_cases hqt : q = t
        · subst hqt
          -- `u` feeds `t`: `c u = J t` and `c t = c u`, against `J t ≠ c t`
          exact absurd ((hP u hq).symm.trans hqu.symm) hJ
        · simp [fire, hqt]; exact hqu
  | @join t hj =>
    intro u
    refine ⟨?_, (hi u).2⟩
    by_cases hut : u = t
    · subst hut
      right; intro p hp
      simp only [fire, ↓reduceIte]
      exact bool_ne_iff.mp (hj p hp)
    · simp only [fire, hut, ↓reduceIte]; exact (hi u).1
  | @fork t hk =>
    intro u
    refine ⟨(hi u).1, fun hK' q hq => ?_⟩
    by_cases hut : u = t
    · subst hut
      simp only [fire, ↓reduceIte] at hK'
      have := bool_ne_iff.mp (hk q hq)
      rw [this, ← hK']
    · simp only [fire, hut, ↓reduceIte] at hK'
      exact (hi u).2 hK' q hq

theorem greach_inv (E : V → V → Prop) {g h : GState V} (hi : Inv E g) (hr : GReach E g h) :
    Inv E h := by
  induction hr with
  | refl => exact hi
  | tail _ hs ih => exact inv_step E ih hs

/-- Under `Inv` a gate step is a stage step or leaves the stages alone. -/
theorem proj_step (E : V → V → Prop) {g h : GState V} (hi : Inv E g) (hs : GStep E g h) :
    h.c = g.c ∨ Step E g.c h.c := by
  cases hs with
  | @stage t hJ hK =>
    right
    exact Step.mk ⟨fun p hp => by rw [((hi t).1.resolve_left hJ) p hp]; exact hJ,
                    fun q hq => (hi t).2 hK q hq⟩
  | join => left; rfl
  | fork => left; rfl

theorem greach_proj (E : V → V → Prop) {g h : GState V} (hi : Inv E g) (hr : GReach E g h) :
    Reach E g.c h.c := by
  induction hr with
  | refl => exact Reach.refl _
  | @tail _ k _ hs ih =>
    rcases proj_step E (greach_inv E hi ‹_›) hs with he | he
    · rw [he]; exact ih
    · exact Reach.tail ih he

omit [DecidableEq V] in
/-- A gate state with no excited gate has no excited stage (no invariant needed). -/
theorem gate_dead_stage_dead (E : V → V → Prop) (g : GState V) (hd : ¬ GLive E g) (t : V) :
    ¬ Excited E g.c t := by
  rintro ⟨hp, hq⟩
  apply hd
  by_cases hJ : g.J t = g.c t
  · exact ⟨t, Or.inr (Or.inl fun p h => by rw [hJ]; exact hp p h)⟩
  · by_cases hK : g.K t = g.c t
    · exact ⟨t, Or.inl ⟨hJ, hK⟩⟩
    · exact ⟨t, Or.inr (Or.inr fun q h => by rw [hq q h]; exact Ne.symm hK)⟩

/-- **H_RENDEZVOUS discharged (one level of C-elements):** from a gate state meeting `Inv`
whose stage bits have no trap, no reachable gate state is a deadlock. -/
theorem gate_deadlock_free (E : V → V → Prop) (hne : Nonempty V) {g h : GState V}
    (hi : Inv E g) (hn : ¬ HasTrap E g.c) (hr : GReach E g h) : GLive E h := by
  refine Classical.byContradiction fun hd => ?_
  obtain ⟨t, ht⟩ := deadlock_free E hne hn (greach_proj E hi hr)
  exact gate_dead_stage_dead E h hd t ht

end Formal.Net.StageNet
