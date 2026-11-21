import Formal.Net.StageNet

/-!
# H_RENDEZVOUS for C-element TREES and buffer chains (shard C, 2026-11-18)

**Problem, plainly.** `StageNetGate` covers one C-element between a stage and its feeders
(join) or consumers (fork). In bdc's circuits there is more in between: a channel's request
passes through its matched delay line (a chain of LUT buffers), joins of more than four inputs
are `bd_ctree` trees of C-elements, a fork's acknowledge can be a tree too. This file proves
the same refinement for any such acyclic network of C-elements (a buffer is a one-input
C-element).

**Gate model.** Stages `V` and gates `G`. Each gate has a nonempty input list `ins g` of stages
and gates, an `owner` stage and a kind (`isJoin`): it is part of its owner's request tree
(join) or acknowledge tree (fork). Stage `t`'s request input is `jroot t` and its acknowledge
input `froot t` (a stage or a gate). A gate fires when all its inputs differ from its output
(C-element; for one input, a buffer); stage `t` fires when its request input differs from it
and its acknowledge input equals it (`C(req, ¬ack)`). One element at a time (H_SI).

**Well-formedness `WF`** (a property of the wiring only): gate inputs that are gates have the
same owner and kind and a smaller `rank` (the trees are acyclic); roots that are gates belong
to the right stage and tree; every gate lies under its owner's root; and the stage leaves of
`t`'s request tree are exactly the stages feeding `t` in `E`, those of its acknowledge tree
exactly the stages `t` feeds.

**Invariant `Inv`** (true at the all-zero reset, `inv_zero`; preserved, `inv_step`): a request-
tree gate either equals its owner or all its inputs equal it; an acknowledge-tree gate that
equals its owner has all its inputs equal to its owner.

**Proved:** `proj_step` (a gate step is a `StageNet.Step` of the stage bits, or leaves them),
`dead_stage_dead` (no excited element => no excited stage), and `tree_deadlock_free`: from a
state meeting `Inv` whose stage bits have no trap, no reachable state of the gate network is a
deadlock. With `StageNet.deadlock_free` this makes research's condition (no token-free closed
walk) sufficient for the C-element circuit, not only for its stage abstraction.

**Not covered:** gates other than C-elements and buffers on the handshake (the steer's and
the mux select's AND gates, the FASTFALL AND in a delay line: with the routing fixed the
steer / select ANDs are a wire or a constant, the FASTFALL gate is not modelled), the mode
changes, the arbiter, timing (H_SI), glitches and X.
-/

namespace Formal.Net.StageNet

/-- An input of a gate or stage: a stage or a gate. -/
inductive Src (V G : Type) where
  | st (v : V)
  | gt (g : G)

structure Wiring (V G : Type) where
  ins : G → List (Src V G)
  owner : G → V
  isJoin : G → Bool
  jroot : V → Src V G
  froot : V → Src V G
  rank : G → Nat

variable {V G : Type} [DecidableEq V] [DecidableEq G]

/-- Gate-network state: stage bits and gate bits. -/
structure TState (V G : Type) where
  c : V → Bool
  w : G → Bool

def TState.val (x : TState V G) : Src V G → Bool
  | .st v => x.c v
  | .gt g => x.w g

/-- `s'` lies in the tree below `s` (inclusive). -/
inductive Below (W : Wiring V G) : Src V G → Src V G → Prop
  | refl (s : Src V G) : Below W s s
  | step {g : G} {i s' : Src V G} : i ∈ W.ins g → Below W i s' → Below W (.gt g) s'

/-- `s` lies in stage `t`'s request tree (`j = true`) or acknowledge tree (`j = false`). -/
def InTree (W : Wiring V G) (t : V) (j : Bool) (s : Src V G) : Prop :=
  ∀ g, s = .gt g → W.owner g = t ∧ W.isJoin g = j

structure WF (E : V → V → Prop) (W : Wiring V G) : Prop where
  ins_ne : ∀ g, W.ins g ≠ []
  ins_gate : ∀ g h, Src.gt h ∈ W.ins g →
    W.owner h = W.owner g ∧ W.isJoin h = W.isJoin g ∧ W.rank h < W.rank g
  jroot_tree : ∀ t, InTree W t true (W.jroot t)
  froot_tree : ∀ t, InTree W t false (W.froot t)
  under_root : ∀ g, Below W (if W.isJoin g then W.jroot (W.owner g) else W.froot (W.owner g)) (.gt g)
  feeders : ∀ p t, E p t ↔ Below W (W.jroot t) (.st p)
  consumers : ∀ t q, E t q ↔ Below W (W.froot t) (.st q)

/-- One speed-independent step of the gate network. -/
inductive TStep (W : Wiring V G) : TState V G → TState V G → Prop
  | stage {x : TState V G} {t : V} : x.val (W.jroot t) ≠ x.c t → x.val (W.froot t) = x.c t →
      TStep W x ⟨fire x.c t, x.w⟩
  | gate {x : TState V G} {g : G} : (∀ i ∈ W.ins g, x.val i ≠ x.w g) →
      TStep W x ⟨x.c, fire x.w g⟩

inductive TReach (W : Wiring V G) : TState V G → TState V G → Prop
  | refl (x : TState V G) : TReach W x x
  | tail {x y z : TState V G} : TReach W x y → TStep W y z → TReach W x z

def TLive (W : Wiring V G) (x : TState V G) : Prop :=
  (∃ t, x.val (W.jroot t) ≠ x.c t ∧ x.val (W.froot t) = x.c t) ∨
  (∃ g, ∀ i ∈ W.ins g, x.val i ≠ x.w g)

def Inv (W : Wiring V G) (x : TState V G) : Prop :=
  ∀ g, (W.isJoin g = true → x.w g = x.c (W.owner g) ∨ ∀ i ∈ W.ins g, x.val i = x.w g) ∧
       (W.isJoin g = false → x.w g = x.c (W.owner g) → ∀ i ∈ W.ins g, x.val i = x.c (W.owner g))

omit [DecidableEq V] [DecidableEq G] in
theorem inv_zero (W : Wiring V G) : Inv W ⟨fun _ => false, fun _ => false⟩ := by
  intro g
  refine ⟨fun _ => Or.inl rfl, fun _ _ i _ => ?_⟩
  cases i <;> rfl

omit [DecidableEq V] [DecidableEq G] in
theorem inTree_input {E : V → V → Prop} {W : Wiring V G} (hw : WF E W) {t : V} {j : Bool}
    {g : G} (hg : InTree W t j (.gt g)) {i : Src V G} (hi : i ∈ W.ins g) : InTree W t j i := by
  rintro h rfl
  obtain ⟨ho, hk, _⟩ := hw.ins_gate g h hi
  obtain ⟨ho', hk'⟩ := hg g rfl
  exact ⟨ho.trans ho', hk.trans hk'⟩

omit [DecidableEq V] [DecidableEq G] in
/-- Request-tree closure: a node of `t`'s request tree that differs from `t` is equal to
everything below it. -/
theorem jclose {E : V → V → Prop} {W : Wiring V G} (hw : WF E W) {x : TState V G}
    (hi : Inv W x) {t : V} {s s' : Src V G} (hb : Below W s s') :
    InTree W t true s → x.val s ≠ x.c t → x.val s' = x.val s := by
  induction hb with
  | refl => intro _ _; rfl
  | @step g i s' hmem _ ih =>
    intro ht hne
    obtain ⟨ho, hk⟩ := ht g rfl
    have hall := ((hi g).1 hk).resolve_left (by rw [ho]; exact hne)
    have hvi : x.val i = x.w g := hall i hmem
    have := ih (inTree_input hw ht hmem) (by rw [hvi]; exact hne)
    rw [this, hvi]; rfl

omit [DecidableEq V] [DecidableEq G] in
/-- Acknowledge-tree closure: a node of `t`'s acknowledge tree that equals `t` has everything
below it equal to `t`. -/
theorem fclose {E : V → V → Prop} {W : Wiring V G} (hw : WF E W) {x : TState V G}
    (hi : Inv W x) {t : V} {s s' : Src V G} (hb : Below W s s') :
    InTree W t false s → x.val s = x.c t → x.val s' = x.c t := by
  induction hb with
  | refl => intro _ h; exact h
  | @step g i s' hmem _ ih =>
    intro ht heq
    obtain ⟨ho, hk⟩ := ht g rfl
    have hvi := (hi g).2 hk (by rw [ho]; exact heq) i hmem
    rw [ho] at hvi
    exact ih (inTree_input hw ht hmem) hvi

omit [DecidableEq V] [DecidableEq G] in
theorem Below.trans {W : Wiring V G} {a b c : Src V G} (h1 : Below W a b) (h2 : Below W b c) :
    Below W a c := by
  induction h1 with
  | refl => exact h2
  | step hm _ ih => exact .step hm (ih h2)

omit [DecidableEq V] [DecidableEq G] in
theorem below_input {W : Wiring V G} {a : Src V G} {g : G} {i : Src V G}
    (h : Below W a (.gt g)) (hi : i ∈ W.ins g) : Below W a i :=
  h.trans (.step hi (.refl i))

theorem bne_iff {a b : Bool} : a ≠ b ↔ a = !b := by cases a <;> cases b <;> simp

theorem inv_step {E : V → V → Prop} {W : Wiring V G} (hw : WF E W) {x y : TState V G}
    (hi : Inv W x) (hs : TStep W x y) : Inv W y := by
  cases hs with
  | @stage t hJ hK =>
    have leavesJ : ∀ p, E p t → x.c p = x.val (W.jroot t) := fun p hp =>
      jclose hw hi ((hw.feeders p t).1 hp) (hw.jroot_tree t) hJ
    have leavesK : ∀ q, E t q → x.c q = x.c t := fun q hq =>
      fclose hw hi ((hw.consumers t q).1 hq) (hw.froot_tree t) hK
    intro g
    have hroot := hw.under_root g
    refine ⟨fun hj => ?_, fun hj hwg => ?_⟩
    · rw [hj] at hroot
      simp only [↓reduceIte] at hroot
      by_cases hut : W.owner g = t
      · -- a request-tree gate of `t` equals `jroot t`, which differs from `t`
        have hv := jclose hw hi hroot (hw.jroot_tree _) (by rw [hut]; exact hJ)
        left
        show x.w g = fire x.c t (W.owner g)
        rw [hut, fire_self, ← bne_iff]
        rw [hut] at hv
        exact fun h => hJ (hv.symm.trans h)
      · have hcu : fire x.c t (W.owner g) = x.c (W.owner g) := fire_ne _ hut
        show x.w g = fire x.c t (W.owner g) ∨ ∀ i ∈ W.ins g, TState.val ⟨fire x.c t, x.w⟩ i = x.w g
        rw [hcu]
        by_cases hwu : x.w g = x.c (W.owner g)
        · exact Or.inl hwu
        · right
          have hall := ((hi g).1 hj).resolve_left hwu
          intro i hmem
          cases i with
          | gt h => exact hall _ hmem
          | st p =>
            have hv : x.c p = x.w g := hall _ hmem
            by_cases hpt : p = t
            · subst hpt
              exfalso
              have hE : E p (W.owner g) := (hw.feeders _ _).2 (below_input hroot hmem)
              exact hwu (hv.symm.trans (leavesK _ hE).symm)
            · show fire x.c t p = x.w g
              rw [fire_ne _ hpt]; exact hv
    · rw [hj] at hroot
      simp only [Bool.false_eq_true, ↓reduceIte] at hroot
      by_cases hut : W.owner g = t
      · exfalso
        have hv := fclose hw hi hroot (hw.froot_tree _) (by rw [hut]; exact hK)
        change x.w g = fire x.c t (W.owner g) at hwg
        rw [hut, fire_self] at hwg
        rw [hut] at hv
        change x.w g = x.c t at hv
        rw [hv] at hwg; cases h0 : x.c t <;> simp [h0] at hwg
      · have hcu : fire x.c t (W.owner g) = x.c (W.owner g) := fire_ne _ hut
        change x.w g = fire x.c t (W.owner g) at hwg
        rw [hcu] at hwg
        have hall := (hi g).2 hj hwg
        intro i hmem
        show TState.val ⟨fire x.c t, x.w⟩ i = fire x.c t (W.owner g)
        rw [hcu]
        cases i with
        | gt h => exact hall _ hmem
        | st q =>
          have hv : x.c q = x.c (W.owner g) := hall _ hmem
          by_cases hqt : q = t
          · subst hqt
            exfalso
            have hE : E (W.owner g) q := (hw.consumers _ _).2 (below_input hroot hmem)
            exact hJ ((leavesJ _ hE).symm.trans hv.symm)
          · show fire x.c t q = _
            rw [fire_ne _ hqt]; exact hv
  | @gate g0 hg =>
    obtain ⟨i0, hi0⟩ := List.exists_mem_of_ne_nil _ (hw.ins_ne g0)
    -- a firing join gate equals its owner; a firing fork gate differs from it
    have hj0 : W.isJoin g0 = true → x.w g0 = x.c (W.owner g0) := fun hj =>
      ((hi g0).1 hj).resolve_right (fun h => hg i0 hi0 (h i0 hi0))
    have hf0 : W.isJoin g0 = false → x.w g0 ≠ x.c (W.owner g0) := fun hj he =>
      hg i0 hi0 (((hi g0).2 hj he i0 hi0).trans he.symm)
    have hself : Src.gt g0 ∉ W.ins g0 := fun h => by
      have := (hw.ins_gate g0 g0 h).2.2; omega
    have hval : ∀ g, Src.gt g0 ∉ W.ins g → ∀ i ∈ W.ins g,
        TState.val ⟨x.c, fire x.w g0⟩ i = x.val i := by
      intro g hn i hmem
      cases i with
      | st p => rfl
      | gt h =>
        show fire x.w g0 h = x.w h
        exact fire_ne _ (fun he => hn (he ▸ hmem))
    intro g
    by_cases hgg : g = g0
    · subst hgg
      refine ⟨fun _ => Or.inr fun i hmem => ?_, fun _ hwg i hmem => ?_⟩
      · rw [hval _ hself i hmem]
        show x.val i = fire x.w g g
        rw [fire_self]; exact bne_iff.mp (hg i hmem)
      · rw [hval _ hself i hmem]
        change fire x.w g g = x.c (W.owner g) at hwg
        rw [fire_self] at hwg
        rw [← hwg]; exact bne_iff.mp (hg i hmem)
    · have hwg' : fire x.w g0 g = x.w g := fire_ne _ hgg
      refine ⟨fun hj => ?_, fun hj hwg => ?_⟩
      · change fire x.w g0 g = x.c (W.owner g) ∨ ∀ i ∈ W.ins g, TState.val ⟨x.c, fire x.w g0⟩ i = fire x.w g0 g
        rw [hwg']
        by_cases hwu : x.w g = x.c (W.owner g)
        · exact Or.inl hwu
        · right
          have hall := ((hi g).1 hj).resolve_left hwu
          have hn : Src.gt g0 ∉ W.ins g := fun hm => by
            obtain ⟨ho, hk, _⟩ := hw.ins_gate g g0 hm
            have := hj0 (hk.trans hj)
            rw [ho] at this
            exact hwu ((hall _ hm).symm.trans this)
          intro i hmem
          rw [hval g hn i hmem]; exact hall i hmem
      · change fire x.w g0 g = x.c (W.owner g) at hwg
        rw [hwg'] at hwg
        have hall := (hi g).2 hj hwg
        have hn : Src.gt g0 ∉ W.ins g := fun hm => by
          obtain ⟨ho, hk, _⟩ := hw.ins_gate g g0 hm
          have := hf0 (hk.trans hj)
          rw [ho] at this
          exact this (hall _ hm)
        intro i hmem
        rw [hval g hn i hmem]; exact hall i hmem

theorem treach_inv {E : V → V → Prop} {W : Wiring V G} (hw : WF E W) {x y : TState V G}
    (hi : Inv W x) (hr : TReach W x y) : Inv W y := by
  induction hr with
  | refl => exact hi
  | tail _ hs ih => exact inv_step hw ih hs

theorem tproj_step {E : V → V → Prop} {W : Wiring V G} (hw : WF E W) {x y : TState V G}
    (hi : Inv W x) (hs : TStep W x y) : y.c = x.c ∨ Step E x.c y.c := by
  cases hs with
  | @stage t hJ hK =>
    right
    refine Step.mk ⟨fun p hp => ?_, fun q hq =>
      fclose hw hi ((hw.consumers t q).1 hq) (hw.froot_tree t) hK⟩
    have h1 : x.c p = x.val (W.jroot t) := jclose hw hi ((hw.feeders p t).1 hp) (hw.jroot_tree t) hJ
    rw [h1]; exact hJ
  | gate => left; rfl

theorem treach_proj {E : V → V → Prop} {W : Wiring V G} (hw : WF E W) {x y : TState V G}
    (hi : Inv W x) (hr : TReach W x y) : Reach E x.c y.c := by
  induction hr with
  | refl => exact Reach.refl _
  | @tail y k hr' hs ih =>
    rcases tproj_step hw (treach_inv hw hi hr') hs with he | he
    · rw [he]; exact ih
    · exact Reach.tail ih he

def srank (W : Wiring V G) : Src V G → Nat
  | .st _ => 0
  | .gt g => W.rank g + 1

omit [DecidableEq V] [DecidableEq G] in
theorem srank_lt {E : V → V → Prop} {W : Wiring V G} (hw : WF E W) {g : G} {i : Src V G}
    (hi : i ∈ W.ins g) : srank W i < srank W (.gt g) := by
  cases i with
  | st _ => simp [srank]
  | gt h => have := (hw.ins_gate g h hi).2.2; simp [srank]; omega

omit [DecidableEq V] [DecidableEq G] in
/-- Descending from a tree node whose value has property `P` while no leaf below it has `P`
finds an excited gate (a C-element whose inputs all differ from it). -/
theorem descend {E : V → V → Prop} {W : Wiring V G} (hw : WF E W) (x : TState V G)
    (P : Bool → Prop) :
    ∀ n, ∀ s, srank W s ≤ n → (∀ p, Below W s (.st p) → ¬ P (x.c p)) → P (x.val s) →
      ∃ g, ∀ i ∈ W.ins g, x.val i ≠ x.w g := by
  intro n
  induction n with
  | zero =>
    intro s hs hl hv
    cases s with
    | st p => exact absurd hv (hl p (.refl _))
    | gt g => simp [srank] at hs
  | succ n ih =>
    intro s hs hl hv
    cases s with
    | st p => exact absurd hv (hl p (.refl _))
    | gt g =>
      by_cases hex : ∀ i ∈ W.ins g, x.val i ≠ x.w g
      · exact ⟨g, hex⟩
      · obtain ⟨i, hmem, hi⟩ : ∃ i ∈ W.ins g, x.val i = x.w g := by
          refine Classical.byContradiction fun hc => hex fun i hm he => hc ⟨i, hm, he⟩
        have hlt := srank_lt hw hmem
        refine ih i (by omega) (fun p hp => hl p (.step hmem hp)) ?_
        rw [hi]; exact hv

omit [DecidableEq V] [DecidableEq G] in
/-- No excited element of the gate network => no excited stage of the stage network. -/
theorem dead_stage_dead {E : V → V → Prop} {W : Wiring V G} (hw : WF E W) (x : TState V G)
    (hd : ¬ TLive W x) (t : V) : ¬ Excited E x.c t := by
  rintro ⟨hp, hq⟩
  apply hd
  by_cases hJ : x.val (W.jroot t) = x.c t
  · -- the request tree sits at `c t` while all its leaves differ: some gate in it is excited
    right
    exact descend hw x (· = x.c t) _ _ (Nat.le_refl _)
      (fun p hb => hp p ((hw.feeders p t).2 hb)) hJ
  · by_cases hK : x.val (W.froot t) = x.c t
    · left; exact ⟨t, hJ, hK⟩
    · right
      exact descend hw x (· ≠ x.c t) _ _ (Nat.le_refl _) (fun q hb hne => hne (hq q ((hw.consumers t q).2 hb))) hK

/-- **H_RENDEZVOUS discharged for C-element trees and buffer chains.** From a state meeting
`Inv` whose stage bits have no trap, no reachable state of the gate network is a deadlock. -/
theorem tree_deadlock_free {E : V → V → Prop} {W : Wiring V G} (hw : WF E W)
    (hne : Nonempty V) {x y : TState V G} (hi : Inv W x) (hn : ¬ HasTrap E x.c)
    (hr : TReach W x y) : TLive W y := by
  refine Classical.byContradiction fun hd => ?_
  obtain ⟨t, ht⟩ := deadlock_free E hne hn (treach_proj hw hi hr)
  exact dead_stage_dead hw y hd t ht

end Formal.Net.StageNet
