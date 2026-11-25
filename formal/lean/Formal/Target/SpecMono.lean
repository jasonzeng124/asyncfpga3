import Formal.Target.Spec
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Floor

/-!
# Formal.Target.SpecMono — how THE statement depends on its parameters

Shard A, 2026-11-06. An addition next to the frozen `Spec.lean` (no definition there changes).

**Problem, plainly.** THE statement `NetCorrectSeq N B A p T R su Δo` has parameters the owner cannot measure
(the guard `g`, the scatter `κ`, the arbiter resolution time `T`) and two harness margins (`su`, `Δo`). To report
"the margin" (the set of parameters at which it holds) one needs to know which way each parameter goes. Shown here,
for every netlist, boundary and arbiter list:
* `seq_anti_T`: proved at `T'` implies proved at every `T ≤ T'` (a larger `T` is a weaker H_ARB, more behaviours);
* `seq_mono_su`, `seq_mono_Δo`: proved at `su` (`Δo`) implies proved at every larger one (a larger margin
  restricts the environment; for `Δo`, it also shortens the window in which `Correct` checks `out0`'s data);
* `seq_anti_p`: proved at `(g', κ')` implies proved at every `(g, κ)` with `0 < g ≤ g'` and `0 ≤ κ ≤ κ'`
  with `κ ≤ 1` (a wider delay window admits more behaviours, and its relation starts later).
So the set of `(g, κ)` at which THE theorem holds is a down-set (the "frontier" the owner asked for is its
boundary), and a result at large `T` and small `su`, `Δo` covers every smaller `T` and larger margins.
The same holds for the pipelined `NetCorrect` (`net_anti_T`, `net_mono_su`, `net_mono_Δo`, `net_anti_p`).

**Not shown.** Anything about `R` (the reset length; `Env` fixes `rst` to exactly `[0, R)`, so there is no
monotonicity); anything about a particular netlist.

**Use for the audit's residual-vacuity row (T5).** By `seq_anti_T`, the headline should be stated at the
LARGEST `T` the arbiters allow; vacuity is the risk at small `T`, and a non-vacuity witness at `T` (C's
`w1_hyps_and_correct`, every `T ≥ 220`) is also one at every larger `T` (`arbOK_mono`).
-/

namespace Formal.Target

/-! ## H_ARB(T) -/

theorem arbOK_mono {T T' : Nat} (h : T ≤ T') {A : List ArbNodes} {x : Beh} (hA : ArbOK T A x) : ArbOK T' A x := by
  intro a ha t1 t2 hc t ht1 ht2
  rw [hA a ha t1 t2 hc t (by omega) ht2, hA a ha t1 t2 hc (t1 + T') (by omega) (by omega)]

theorem seq_anti_T {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T T' R su Δo : Nat} (hT : T ≤ T')
    (h : NetCorrectSeq N B A p T' R su Δo) : NetCorrectSeq N B A p T R su Δo :=
  fun x n va vb hb ha he hs => h x n va vb hb (arbOK_mono hT ha) he hs

theorem net_anti_T {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T T' R su Δo : Nat} (hT : T ≤ T')
    (h : NetCorrect N B A p T' R su Δo) : NetCorrect N B A p T R su Δo :=
  fun x n va vb hb ha he => h x n va vb hb (arbOK_mono hT ha) he

/-! ## The harness margins `su`, `Δo` -/

theorem envIn_mono_su {x : Beh} {ch : InCh} {R su su' : Nat} {n : Option Nat} {vals : Nat → Nat} (h : su ≤ su')
    (he : EnvIn x ch R su' n vals) : EnvIn x ch R su n vals := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := he
  exact ⟨h1, h2, h3, h4, fun t ht hr hr' s hs hs' => h5 t ht hr hr' s (by omega) hs', h6⟩

theorem envOut_mono_Δo {x : Beh} {ch : OutCh} {R Δo Δo' : Nat} (h : Δo ≤ Δo') (he : EnvOut x ch R Δo') :
    EnvOut x ch R Δo := by
  obtain ⟨h1, h2, h3, h4⟩ := he
  exact ⟨h1, h2, h3, fun t ht ha ha' s hs hs' => h4 t ht ha ha' s (by omega) hs'⟩

theorem env_mono {x : Beh} {B : Boundary} {R su su' Δo Δo' : Nat} {n : Option Nat} {va vb : Nat → Nat}
    (hs : su ≤ su') (hd : Δo ≤ Δo') (he : Env x B R su' Δo' n va vb) : Env x B R su Δo n va vb := by
  obtain ⟨h1, h2, h3, ha, hb, hst, ho, hp⟩ := he
  exact ⟨h1, h2, h3, envIn_mono_su hs ha, envIn_mono_su hs hb, envIn_mono_su hs hst, envOut_mono_Δo hd ho,
    envOut_mono_Δo hd hp⟩

theorem correct_mono_Δo {x : Beh} {B : Boundary} {R Δo Δo' : Nat} {n : Option Nat} {va vb : Nat → Nat}
    (hd : Δo ≤ Δo') (hc : Correct x B R Δo n va vb) : Correct x B R Δo' n va vb := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, fun t0 t hR hr hr' ht hw => h6 t0 t hR hr hr' (by omega) hw, h7⟩

theorem seq_mono_su {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T R su su' Δo : Nat}
    (hs : su ≤ su') (h : NetCorrectSeq N B A p T R su Δo) : NetCorrectSeq N B A p T R su' Δo :=
  fun x n va vb hb ha he hq => h x n va vb hb ha (env_mono hs le_rfl he) hq

theorem seq_mono_Δo {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T R su Δo Δo' : Nat}
    (hd : Δo ≤ Δo') (h : NetCorrectSeq N B A p T R su Δo) : NetCorrectSeq N B A p T R su Δo' :=
  fun x n va vb hb ha he hq => correct_mono_Δo hd (h x n va vb hb ha (env_mono le_rfl hd he) hq)

theorem net_mono_su {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T R su su' Δo : Nat}
    (hs : su ≤ su') (h : NetCorrect N B A p T R su Δo) : NetCorrect N B A p T R su' Δo :=
  fun x n va vb hb ha he => h x n va vb hb ha (env_mono hs le_rfl he)

theorem net_mono_Δo {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T R su Δo Δo' : Nat}
    (hd : Δo ≤ Δo') (h : NetCorrect N B A p T R su Δo) : NetCorrect N B A p T R su Δo' :=
  fun x n va vb hb ha he => correct_mono_Δo hd (h x n va vb hb ha (env_mono le_rfl hd he))

/-! ## The delay parameters `(g, κ)` -/

/-- `p` is inside `p'`: `0 < g ≤ g'` and `0 ≤ κ ≤ κ'`, with `κ ≤ 1` (above 1 the lower window end is negative and
a larger guard would RAISE it, so the windows are not nested). -/
def DelayPar.LE (p p' : DelayPar) : Prop := 0 < p.g ∧ p.g ≤ p'.g ∧ 0 ≤ p.κ ∧ p.κ ≤ p'.κ ∧ p.κ ≤ 1

theorem lerp_nonneg (a b : Nat) {c : ℚ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : 0 ≤ lerp a b c := by
  unfold lerp
  have : (0 : ℚ) ≤ 1 - c := by linarith
  exact add_nonneg (mul_nonneg this (Nat.cast_nonneg _)) (mul_nonneg h0 (Nat.cast_nonneg _))

/-- The admissible window at `p` lies inside the one at `p'`. -/
theorem adm_mono {p p' : DelayPar} (hp : p.LE p') {c : ℚ} (h0 : 0 ≤ c) (h1 : c ≤ 1) {e : Arc} {d : Nat}
    (h : Adm p c e d) : Adm p' c e d := by
  obtain ⟨hg0, hgg, hk0, hkk, hk1⟩ := hp
  obtain ⟨hlo, hhi⟩ := h
  have hlo0 := lerp_nonneg e.fmin e.smin h0 h1
  have hhi0 := lerp_nonneg e.fmax e.smax h0 h1
  have hg0' : 0 < p'.g := lt_of_lt_of_le hg0 hgg
  refine ⟨le_trans ?_ hlo, le_trans hhi ?_⟩
  · -- (1-κ')·lo/g' ≤ (1-κ)·lo/g
    rcases le_or_gt (1 - p'.κ) 0 with hneg | hpos
    · have : (1 - p'.κ) * lerp e.fmin e.smin c / p'.g ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg hlo0) hg0'.le
      have : 0 ≤ (1 - p.κ) * lerp e.fmin e.smin c / p.g :=
        div_nonneg (mul_nonneg (by linarith) hlo0) hg0.le
      linarith
    · have hA : (1 - p'.κ) * lerp e.fmin e.smin c ≤ (1 - p.κ) * lerp e.fmin e.smin c :=
        mul_le_mul_of_nonneg_right (by linarith) hlo0
      calc (1 - p'.κ) * lerp e.fmin e.smin c / p'.g ≤ (1 - p'.κ) * lerp e.fmin e.smin c / p.g :=
            div_le_div_of_nonneg_left (mul_nonneg hpos.le hlo0) hg0 hgg
        _ ≤ (1 - p.κ) * lerp e.fmin e.smin c / p.g := div_le_div_of_nonneg_right hA hg0.le
  · have h1k : (0 : ℚ) ≤ 1 + p.κ := by linarith
    calc (1 + p.κ) * lerp e.fmax e.smax c * p.g ≤ (1 + p'.κ) * lerp e.fmax e.smax c * p.g := by
          apply mul_le_mul_of_nonneg_right _ hg0.le
          exact mul_le_mul_of_nonneg_right (by linarith) hhi0
      _ ≤ (1 + p'.κ) * lerp e.fmax e.smax c * p'.g :=
          mul_le_mul_of_nonneg_left hgg (mul_nonneg (by linarith) hhi0)

theorem foldr_max_mono {l : List Arc} {f f' : Arc → Nat} (h : ∀ e, f e ≤ f' e) :
    (l.map f).foldr max 0 ≤ (l.map f').foldr max 0 := by
  induction l with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le_max (h e) ih

theorem rat_ceil_eq' (q : ℚ) : Rat.ceil q = ⌈q⌉ := by
  rw [Rat.ceil_eq_neg_floor_neg]; rfl

/-- A wider window starts its relation no earlier. -/
theorem start_mono {p p' : DelayPar} (hp : p.LE p') (g : Gate) : g.start p ≤ g.start p' := by
  obtain ⟨hg0, hgg, hk0, hkk, -⟩ := hp
  unfold Gate.start
  apply foldr_max_mono
  intro e
  rw [rat_ceil_eq', rat_ceil_eq']
  apply Int.toNat_le_toNat
  apply Int.ceil_mono
  have hs : (0 : ℚ) ≤ e.smax := Nat.cast_nonneg _
  calc (1 + p.κ) * e.smax * p.g ≤ (1 + p'.κ) * e.smax * p.g := by
        apply mul_le_mul_of_nonneg_right _ hg0.le
        exact mul_le_mul_of_nonneg_right (by linarith) hs
    _ ≤ (1 + p'.κ) * e.smax * p'.g := mul_le_mul_of_nonneg_left hgg (mul_nonneg (by linarith) hs)

theorem gateOK_mono {p p' : DelayPar} (hp : p.LE p') {c : ℚ} (h0 : 0 ≤ c) (h1 : c ≤ 1) {g : Gate} {x : Beh}
    (h : GateOK p c g x) : GateOK p' c g x := by
  obtain ⟨f, hm, ht⟩ := h
  refine ⟨f, hm, fun t hs => ?_⟩
  have := ht t (le_trans (start_mono hp g) hs)
  exact ⟨fun i hi => ⟨(this.1 i hi).1, adm_mono hp h0 h1 (this.1 i hi).2⟩, this.2⟩

theorem behaves_mono {p p' : DelayPar} (hp : p.LE p') {N : Net} {x : Beh} (h : Behaves p N x) : Behaves p' N x := by
  obtain ⟨c, h0, h1, hg⟩ := h
  exact ⟨c, h0, h1, fun g hg' => gateOK_mono hp h0 h1 (hg g hg')⟩

/-- **The margin is a down-set:** THE (sequential) statement at `p'` implies it at every `p` inside `p'`. -/
theorem seq_anti_p {N : Net} {B : Boundary} {A : List ArbNodes} {p p' : DelayPar} {T R su Δo : Nat}
    (hp : p.LE p') (h : NetCorrectSeq N B A p' T R su Δo) : NetCorrectSeq N B A p T R su Δo :=
  fun x n va vb hb ha he hs => h x n va vb (behaves_mono hp hb) ha he hs

theorem net_anti_p {N : Net} {B : Boundary} {A : List ArbNodes} {p p' : DelayPar} {T R su Δo : Nat}
    (hp : p.LE p') (h : NetCorrect N B A p' T R su Δo) : NetCorrect N B A p T R su Δo :=
  fun x n va vb hb ha he => h x n va vb (behaves_mono hp hb) ha he

/-- All five at once: proved at `(p', T', su, Δo)` gives every `(p, T, su', Δo')` with `p` inside `p'`,
`T ≤ T'`, `su ≤ su'`, `Δo ≤ Δo'`. -/
theorem seq_weaken {N : Net} {B : Boundary} {A : List ArbNodes} {p p' : DelayPar} {T T' R su su' Δo Δo' : Nat}
    (hp : p.LE p') (hT : T ≤ T') (hs : su ≤ su') (hd : Δo ≤ Δo') (h : NetCorrectSeq N B A p' T' R su Δo) :
    NetCorrectSeq N B A p T R su' Δo' :=
  seq_mono_Δo hd (seq_mono_su hs (seq_anti_T hT (seq_anti_p hp h)))

end Formal.Target
