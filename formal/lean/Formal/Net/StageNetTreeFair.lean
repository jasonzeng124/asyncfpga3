import Formal.Net.StageNetTree

/-!
# Fair runs of the C-element gate network fire every stage infinitely often (shard C, 2026-11-18)

**Problem, plainly.** `StageNetTree.tree_deadlock_free` says the gate network (stage
controllers, C-element / buffer trees between them) never reaches a state where nothing can
move. That still allows part of it to starve while another part runs. This file proves that
cannot happen: in every weakly fair infinite run (every excited stage controller or tree gate
eventually fires) from a state meeting `Inv` whose stage bits have no trap, EVERY stage fires
infinitely often.

**Proof.** The stage bits of a gate run are a `StageNet` run with stutter steps (`tproj_step`).
They are fair at the stage level (`proj_fair`): if a stage `t` is excited in the stage model and
never fires again, its neighbours never fire again either (each would need `t` to agree / differ
the other way), so the gates of its request and acknowledge trees see constant leaves and fire
at most once more each (by induction on rank); once they are still, no gate in `t`'s trees is
excited (fairness), so by the descent argument `t`'s own controller is excited, and fairness
fires it. Then `StageNet.fair_all_fire` applies.

Hypotheses: `WF` (wiring), `Inv` at the start (true at the all-zero reset), no trap in the
start's stage bits, finite stage and gate sets (lists), weak fairness (H_CEL_FAIR for every
gate). Not covered: as in `StageNetTree` (fixed mode; AND gates on the handshake; arbiter;
timing; glitches; X).
-/

namespace Formal.Net.StageNet

variable {V G : Type} [DecidableEq V] [DecidableEq G]

def TRun (W : Wiring V G) (r : Nat → TState V G) : Prop := ∀ n, TStep W (r n) (r (n + 1))

def SEx (W : Wiring V G) (x : TState V G) (t : V) : Prop :=
  x.val (W.jroot t) ≠ x.c t ∧ x.val (W.froot t) = x.c t

def GEx (W : Wiring V G) (x : TState V G) (g : G) : Prop := ∀ i ∈ W.ins g, x.val i ≠ x.w g

/-- Weak fairness for every element of the gate network. -/
def TFair (W : Wiring V G) (r : Nat → TState V G) : Prop :=
  (∀ n t, SEx W (r n) t → ∃ m, n ≤ m ∧ (r (m + 1)).c t ≠ (r m).c t) ∧
  (∀ n g, GEx W (r n) g → ∃ m, n ≤ m ∧ (r (m + 1)).w g ≠ (r m).w g)

theorem trun_reach {W : Wiring V G} {r : Nat → TState V G} (hr : TRun W r) :
    ∀ n, TReach W (r 0) (r n)
  | 0 => TReach.refl _
  | n + 1 => TReach.tail (trun_reach hr n) (hr n)

/-- In the stage model an excited stage stays excited while others fire. -/
theorem excited_persist {E : V → V → Prop} {x : State V} {t a : V} (ht : Excited E x t)
    (ha : Excited E x a) (hat : a ≠ t) : Excited E (fire x a) t := by
  rw [excited_iff_noZ] at ht ⊢
  intro b hb
  by_cases hba : b = a
  · subst hba
    exact (excited_iff_noZ E x b).1 ha t ((Z_fire_out E x (Ne.symm hat)).1 hb)
  · exact ht b ((Z_fire_ne E x hba (Ne.symm hat)).1 hb)

omit [DecidableEq V] [DecidableEq G] in
/-- `descend`, also saying where the excited gate is. -/
theorem descend' {E : V → V → Prop} {W : Wiring V G} (hw : WF E W) (x : TState V G)
    (P : Bool → Prop) :
    ∀ n, ∀ s, srank W s ≤ n → (∀ p, Below W s (.st p) → ¬ P (x.c p)) → P (x.val s) →
      ∃ g, Below W s (.gt g) ∧ ∀ i ∈ W.ins g, x.val i ≠ x.w g := by
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
      · exact ⟨g, .refl _, hex⟩
      · obtain ⟨i, hmem, hi⟩ : ∃ i ∈ W.ins g, x.val i = x.w g := by
          refine Classical.byContradiction fun hc => hex fun i hm he => hc ⟨i, hm, he⟩
        have hlt := srank_lt hw hmem
        obtain ⟨g', hb, he⟩ := ih i (by omega) (fun p hp => hl p (.step hmem hp)) (by rw [hi]; exact hv)
        exact ⟨g', .step hmem hb, he⟩

/-- Stable from `N`: the value of `i` does not change at or after `N`. -/
def Stable (r : Nat → TState V G) (i : Src V G) (N : Nat) : Prop := ∀ m, N ≤ m → (r m).val i = (r N).val i

omit [DecidableEq V] [DecidableEq G] in
theorem Stable.mono {r : Nat → TState V G} {i : Src V G} {N N' : Nat} (h : Stable r i N)
    (hN : N ≤ N') : Stable r i N' := fun m hm => (h m (Nat.le_trans hN hm)).trans (h N' hN).symm

omit [DecidableEq V] [DecidableEq G] in
theorem stable_list {r : Nat → TState V G} :
    ∀ (l : List (Src V G)), (∀ i ∈ l, ∃ N, Stable r i N) → ∃ N, ∀ i ∈ l, Stable r i N
  | [], _ => ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | i :: l, h => by
    obtain ⟨N1, h1⟩ := h i List.mem_cons_self
    obtain ⟨N2, h2⟩ := stable_list l (fun j hj => h j (List.mem_cons_of_mem _ hj))
    refine ⟨max N1 N2, fun j hj => ?_⟩
    rcases List.mem_cons.mp hj with rfl | hj
    · exact h1.mono (Nat.le_max_left _ _)
    · exact (h2 j hj).mono (Nat.le_max_right _ _)

theorem tstep_cases {W : Wiring V G} {x y : TState V G} (h : TStep W x y) :
    (∃ t, SEx W x t ∧ y = ⟨fire x.c t, x.w⟩) ∨ (∃ g, GEx W x g ∧ y = ⟨x.c, fire x.w g⟩) := by
  cases h with
  | stage hJ hK => exact Or.inl ⟨_, ⟨hJ, hK⟩, rfl⟩
  | gate hg => exact Or.inr ⟨_, hg, rfl⟩

omit [DecidableEq V] [DecidableEq G] in
/-- Induction from `N` upward. -/
theorem from_ind {P : Nat → Prop} {N : Nat} (h0 : P N) (hs : ∀ m, N ≤ m → P m → P (m + 1)) :
    ∀ m, N ≤ m → P m := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = N + k := ⟨m - N, by omega⟩
  induction k with
  | zero => exact h0
  | succ k ih => exact hs (N + k) (by omega) (ih (by omega))

/-- A gate whose inputs are stable from `N0` is stable from some later time. -/
theorem gate_settles {W : Wiring V G} {r : Nat → TState V G} (hr : TRun W r) {g : G} {N0 : Nat}
    (hin : ∀ i ∈ W.ins g, Stable r i N0) (hne : W.ins g ≠ []) : ∃ N, Stable r (.gt g) N := by
  by_cases hf : ∃ m, N0 ≤ m ∧ (r (m + 1)).w g ≠ (r m).w g
  · obtain ⟨m1, hm1, hfm⟩ := hf
    -- at m1 the gate fired: afterwards it equals its (constant) inputs
    have hfire : ∀ i ∈ W.ins g, (r (m1 + 1)).val i = (r (m1 + 1)).w g := by
      rcases tstep_cases (hr m1) with ⟨t, _, hy⟩ | ⟨g0, hg0, hy⟩
      · exact absurd (by rw [hy]) hfm
      · by_cases hgg : g = g0
        · subst hgg
          intro i hi
          have h2 : (r (m1 + 1)).val i = (r m1).val i :=
            ((hin i hi) (m1 + 1) (by omega)).trans ((hin i hi) m1 hm1).symm
          rw [h2, hy]
          show (r m1).val i = fire (r m1).w g g
          rw [fire_self]; exact bne_iff.mp (hg0 i hi)
        · exfalso; apply hfm; rw [hy]; exact fire_ne _ hgg
    refine ⟨m1 + 1, from_ind rfl fun m hm ih => ?_⟩
    rw [← ih]
    rcases tstep_cases (hr m) with ⟨t, _, hy⟩ | ⟨g0, hg0, hy⟩
    · rw [hy]; rfl
    · by_cases hgg : g = g0
      · subst hgg
        exfalso
        obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hne
        apply hg0 i hi
        have h1 : (r m).val i = (r (m1 + 1)).val i :=
          ((hin i hi) m (by omega)).trans ((hin i hi) (m1 + 1) (by omega)).symm
        rw [h1, hfire i hi]; exact ih.symm
      · rw [hy]; show fire (r m).w g0 g = (r m).w g
        exact fire_ne _ hgg
  · refine ⟨N0, from_ind rfl fun m hm ih => ?_⟩
    rw [← ih]
    exact Classical.byContradiction fun h => hf ⟨m, hm, h⟩

/-- **Stage-level fairness of a fair gate run.** -/
theorem proj_fair {E : V → V → Prop} {W : Wiring V G} (hw : WF E W) (gates : List G)
    (hgates : ∀ g, g ∈ gates) {r : Nat → TState V G} (hr : TRun W r) (hf : TFair W r)
    (hi : Inv W (r 0)) : Fair E (fun n => (r n).c) := by
  intro n t hex
  refine Classical.byContradiction fun hno => ?_
  have hnf : ∀ m, n ≤ m → (r (m + 1)).c t = (r m).c t := fun m hm =>
    Classical.byContradiction fun h => hno ⟨m, hm, h⟩
  have hinv : ∀ m, Inv W (r m) := fun m => treach_inv hw hi (trun_reach hr m)
  have hstep : ∀ m, (r (m + 1)).c = (r m).c ∨ Step E (r m).c (r (m + 1)).c :=
    fun m => tproj_step hw (hinv m) (hr m)
  -- (i) t stays excited
  have hexm : ∀ m, n ≤ m → Excited E (r m).c t := from_ind hex fun m hm ih => by
    rcases hstep m with h | h
    · rw [h]; exact ih
    · obtain ⟨a, ha, hy⟩ := step_fire h
      rw [hy]
      by_cases hat : a = t
      · subst hat
        exfalso
        have := hnf m hm
        rw [hy, fire_self] at this
        cases h0 : (r m).c a <;> simp [h0] at this
      · exact excited_persist ih ha hat
  -- (ii) its neighbours never fire
  have hnb : ∀ p, (E p t ∨ E t p) → Stable r (.st p) n := fun p hp => from_ind rfl fun m hm ih => by
    have ih' : (r m).c p = (r n).c p := ih
    show (r (m + 1)).c p = (r n).c p
    rw [← ih']
    rcases hstep m with h | h
    · rw [h]
    · obtain ⟨a, ha, hy⟩ := step_fire h
      rw [hy]
      by_cases hap : a = p
      · subst hap
        exfalso
        obtain ⟨htp, htq⟩ := hexm m hm
        rcases hp with hp | hp
        · exact htp a hp (ha.2 t hp).symm
        · exact ha.1 t hp (htq a hp).symm
      · exact fire_ne _ (Ne.symm hap)
  -- (iii) every gate of t's trees settles
  let InT : G → Prop := fun g => Below W (W.jroot t) (.gt g) ∨ Below W (W.froot t) (.gt g)
  have hset : ∀ k, ∀ g, W.rank g < k → InT g → ∃ N, Stable r (.gt g) N := by
    intro k
    induction k with
    | zero => intro g h; omega
    | succ k ih =>
      intro g hk hg
      have hin : ∀ i ∈ W.ins g, ∃ N, Stable r i N := by
        intro i hmem
        cases i with
        | st p =>
          refine ⟨n, hnb p ?_⟩
          rcases hg with hb | hb
          · exact Or.inl ((hw.feeders p t).2 (below_input hb hmem))
          · exact Or.inr ((hw.consumers t p).2 (below_input hb hmem))
        | gt h =>
          have hlt := (hw.ins_gate g h hmem).2.2
          exact ih h (by omega) (hg.elim (fun hb => Or.inl (below_input hb hmem))
            (fun hb => Or.inr (below_input hb hmem)))
      obtain ⟨N0, hN0⟩ := stable_list _ hin
      exact gate_settles hr hN0 (hw.ins_ne g)
  have hset' : ∀ g, ∃ N, InT g → Stable r (.gt g) N := fun g => by
    by_cases hg : InT g
    · obtain ⟨N, hN⟩ := hset (W.rank g + 1) g (by omega) hg; exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hg⟩
  let f : G → Nat := fun g => Classical.choose (hset' g)
  have hfs : ∀ g, InT g → Stable r (.gt g) (f g) := fun g => Classical.choose_spec (hset' g)
  let N2 := max n (maxOn f gates)
  -- (iv) from N2 no gate of t's trees is excited
  have hquiet : ∀ g, InT g → ¬ GEx W (r N2) g := by
    intro g hg he
    obtain ⟨m, hm, hch⟩ := hf.2 N2 g he
    have hle : f g ≤ N2 := Nat.le_trans (le_maxOn f (hgates g)) (Nat.le_max_right _ _)
    have h1 := hfs g hg (m + 1) (by omega)
    have h2 := hfs g hg m (by omega)
    exact hch (h1.trans h2.symm)
  obtain ⟨hp, hq⟩ := hexm N2 (Nat.le_max_left _ _)
  by_cases hJ : (r N2).val (W.jroot t) = (r N2).c t
  · obtain ⟨g, hb, he⟩ := descend' hw (r N2) (· = (r N2).c t) _ _ (Nat.le_refl _)
      (fun p hb => hp p ((hw.feeders p t).2 hb)) hJ
    exact hquiet g (Or.inl hb) he
  · by_cases hK : (r N2).val (W.froot t) = (r N2).c t
    · obtain ⟨m, hm, hch⟩ := hf.1 N2 t ⟨hJ, hK⟩
      exact hch (hnf m (Nat.le_trans (Nat.le_max_left _ _) hm))
    · obtain ⟨g, hb, he⟩ := descend' hw (r N2) (· ≠ (r N2).c t) _ _ (Nat.le_refl _)
        (fun q hb hne => hne (hq q ((hw.consumers t q).2 hb))) hK
      exact hquiet g (Or.inr hb) he

/-- **Every stage of the gate network fires infinitely often** in every weakly fair run from a
state meeting `Inv` whose stage bits have no trap. -/
theorem tree_fair_all_fire {E : V → V → Prop} {W : Wiring V G} (hw : WF E W)
    (nodes : List V) (hnodes : ∀ v, v ∈ nodes) (gates : List G) (hgates : ∀ g, g ∈ gates)
    {r : Nat → TState V G} (hr : TRun W r) (hf : TFair W r) (hi : Inv W (r 0))
    (hn : ¬ HasTrap E (r 0).c) : ∀ v N, ∃ m, N ≤ m ∧ (r (m + 1)).c v ≠ (r m).c v :=
  fair_all_fire (r := fun n => (r n).c) E nodes hnodes
    (fun m => tproj_step hw (treach_inv hw hi (trun_reach hr m)) (hr m))
    (proj_fair hw gates hgates hr hf hi) hn

end Formal.Net.StageNet
