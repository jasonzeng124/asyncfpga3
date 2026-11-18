import Formal.Rewrite.IncCmp2Lib

/-!
# Formal.Rewrite.ChanInv — a reachable-state channel invariant for imported graphs (shard A, 2026-11-18)

Core Lean only.

**Problem, plainly.** For a lockstep argument about an imported graph (`graph rs`, `natVI` semantics) we want
to know that every token that ever sits on channel `ch` satisfies a predicate `Q ch`. For most rules this is
local: from `Q`-inputs the rule pushes `Q`-outputs (`RuleSafe`). A `cond_br` is not local: the value it sends
to the true side is only good because a compare, computed on a parallel path from a copy of the same token,
came out true. So the invariant must also relate the condition tokens to the data tokens, in order.

**Proved.**
* `RuleSafe` sufficient conditions per rule kind: `comp_safe` (pointwise `Pw`), `comp1_safe`, `comp2_safe`,
  `comp_safe_triv`, `fork_safe`, `branch_safe`, `mux_safe`, `cm_safe`, `sink_safe`.
* A branch `Pair` (`lF: fork e [d0, x]`, optional `lA: comp [d0] d fA` (`hasA`; otherwise `d0 = d`),
  `lC: comp [x, k] c F`, `lK: fork c os` with `cb ∈ os`, `lB: branch cb d t f`), with private channels
  `d0 d x c cb` and the hypothesis `F(v, w)` true `→ Q t (g v)` (`PairOK`). Its relational invariant
  `PairInv` (a list `W` of in-flight values in fork order, data side and condition side both aligned with it,
  every true condition paired with a `Q t` value) holds on empty private channels (`pairInv_empty`), is
  preserved by EVERY step of `graph rs` (`pair_step`), and gives `Q t` for the value a true firing of `lB`
  pushes (`pairInv_head`).
* `chan_inv`: if every label that is not some pair's `lB` holds a `RuleSafe` rule and every pair satisfies
  `PairOK`, then from any `Q`-store with the pairs' private channels empty, every store reached by a `Run` is a
  `Q`-store and satisfies every pair's `PairInv`. `chan_inv_true` is the true-side corollary.
  Any number of pairs; they need not be disjoint beyond what each pair's own `priv` hypothesis says.

**Not covered:** per-graph discharge of the hypotheses (countloop's two pairs are the intended instance);
a compare reading its data token from anything but a fork beside the branch's data path; `mux`/`cm` on the
private channels (they are excluded by `priv`).
-/

namespace Formal.Rewrite.ChanInv

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

/-! ## Store invariants and per-rule safety -/

/-- Every token on channel `ch` satisfies `Q ch`. -/
def SInv (Q : Nat → Nat → Prop) (σ : Store Nat Nat) : Prop := ∀ ch v, v ∈ σ ch → Q ch v

/-- Firing `r` from a `Q`-store only pushes `Q`-values. -/
def RuleSafe (Q : Nat → Nat → Prop) (r : Rule) : Prop :=
  ∀ σ fr, SInv Q σ → r.fire natVI σ = some fr → ∀ ch v, v ∈ fr.2 ch → Q ch v

/-- Pointwise relation between two lists of the same length. -/
def Pw (R : Nat → Nat → Prop) : List Nat → List Nat → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Pw R as bs
  | _, _ => False

theorem heads_forall2 {σ : Store Nat Nat} : ∀ {cs vs : List Nat}, heads σ cs = some vs →
    Pw (fun c v => v ∈ σ c) cs vs
  | [], vs, h => by simp only [heads, Option.some.injEq] at h; subst h; exact trivial
  | c :: cs, vs, h => by
    simp only [heads] at h
    split at h
    · cases h
    · rename_i v rest hc
      cases hh : heads σ cs with
      | none => rw [hh] at h; cases h
      | some ws =>
        rw [hh] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
        exact ⟨by show v ∈ σ c; rw [hc]; simp, heads_forall2 hh⟩

theorem pw_imp {R S : Nat → Nat → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {as bs : List Nat}, Pw R as bs → Pw S as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, h' => ⟨h _ _ h'.1, pw_imp h h'.2⟩
  | [], _ :: _, h' => h'.elim
  | _ :: _, [], h' => h'.elim

theorem sinv_apply {Q : Nat → Nat → Prop} {σ : Store Nat Nat} {fr : Fire Nat Nat} (h : SInv Q σ)
    (hp : ∀ ch v, v ∈ fr.2 ch → Q ch v) : SInv Q (applyF σ fr) := by
  intro ch v hv
  simp only [applyF, List.mem_append] at hv
  rcases hv with hv | hv
  · exact h ch v (List.mem_of_mem_drop hv)
  · exact hp ch v hv

/-- A one-input strict rule fires on the head of its input. -/
theorem fire1 {i : Nat} {g : List Nat → Option (Nat → List Nat)} {σ : Store Nat Nat} {fr : Fire Nat Nat}
    (h : strictF [i] g σ = some fr) : ∃ v vs out, σ i = v :: vs ∧ g [v] = some out ∧ fr = (popOf [i], out) := by
  obtain ⟨ws, out, hh, hg, rfl⟩ := strictF_some h
  simp only [heads] at hh
  split at hh
  · cases hh
  · rename_i v vs hv
    simp only [Option.map_some, Option.some.injEq] at hh; subst hh
    exact ⟨v, vs, out, hv, hg, rfl⟩

theorem fire_fork {i : Nat} {os : List Nat} {σ : Store Nat Nat} {fr : Fire Nat Nat}
    (h : (Rule.fork i os).fire natVI σ = some fr) :
    ∃ v vs, σ i = v :: vs ∧ fr = (popOf [i], fun c => if c ∈ os then [v] else []) := by
  obtain ⟨v, vs, out, hv, hg, rfl⟩ := fire1 (g := (Rule.fork i os).out natVI) h
  simp only [Rule.out, Option.some.injEq] at hg; subst hg
  exact ⟨v, vs, hv, by simp⟩

theorem fire_branch {c d t f : Nat} {σ : Store Nat Nat} {fr : Fire Nat Nat}
    (h : (Rule.branch c d t f).fire natVI σ = some fr) :
    ∃ b bs y ys, σ c = b :: bs ∧ σ d = y :: ys ∧
      fr = (popOf [c, d], fun ch => (if ch = t ∧ b % 2 = 1 then [y] else []) ++
        (if ch = f ∧ ¬ b % 2 = 1 then [y] else [])) := by
  have h' : strictF [c, d] ((Rule.branch c d t f).out natVI) σ = some fr := h
  obtain ⟨ws, out, hh, hg, rfl⟩ := strictF_some h'
  simp only [heads] at hh
  split at hh
  · cases hh
  · rename_i b bs hb
    split at hh
    · cases hh
    · rename_i y ys hy
      simp only [Option.map_some, Option.some.injEq] at hh; subst hh
      simp only [Rule.out, natVI, Option.map_some, Option.some.injEq] at hg; subst hg
      refine ⟨b, bs, y, ys, hb, hy, ?_⟩
      congr 1; funext ch
      by_cases hb1 : b % 2 = 1
      · simp [hb1]
      · simp [hb1]

/-! ### Sufficient conditions, one per rule kind -/

section Safe
variable {Q : Nat → Nat → Prop}

theorem comp_safe {ins : List Nat} {o : Nat} {e : E} (h : ∀ vs, Pw Q ins vs → Q o (e.eval vs)) :
    RuleSafe Q (.comp ins o e) := by
  intro σ fr hσ hf ch v hv
  have hf' : strictF ins ((Rule.comp ins o e).out natVI) σ = some fr := hf
  obtain ⟨vs, out, hh, hg, rfl⟩ := strictF_some hf'
  simp only [Rule.out, Option.some.injEq] at hg; subst hg
  simp only at hv
  split at hv
  · rename_i hc; subst hc
    simp only [List.mem_singleton] at hv; subst hv
    exact h vs (pw_imp (fun c w hw => hσ c w hw) (heads_forall2 hh))
  · cases hv

theorem comp1_safe {i o : Nat} {e : E} (h : ∀ v, Q i v → Q o (e.eval [v])) : RuleSafe Q (.comp [i] o e) :=
  comp_safe fun vs hvs => by
    match vs, hvs with
    | [v], hvs => exact h v hvs.1

theorem comp2_safe {i j o : Nat} {e : E} (h : ∀ a b, Q i a → Q j b → Q o (e.eval [a, b])) :
    RuleSafe Q (.comp [i, j] o e) :=
  comp_safe fun vs hvs => by
    match vs, hvs with
    | [a, b], hvs => exact h a b hvs.1 hvs.2.1

/-- A `comp` whose output channel is unconstrained. -/
theorem comp_safe_triv {ins : List Nat} {o : Nat} {e : E} (h : ∀ v, Q o v) : RuleSafe Q (.comp ins o e) :=
  comp_safe fun _ _ => h _

theorem fork_safe {i : Nat} {os : List Nat} (h : ∀ o ∈ os, ∀ v, Q i v → Q o v) : RuleSafe Q (.fork i os) := by
  intro σ fr hσ hf ch v hv
  obtain ⟨w, ws, hw, rfl⟩ := fire_fork hf
  simp only at hv
  split at hv
  · rename_i hc
    simp only [List.mem_singleton] at hv; subst hv
    exact h ch hc v (hσ i v (by rw [hw]; simp))
  · cases hv

theorem branch_safe {c d t f : Nat} (h : ∀ v, Q d v → Q t v ∧ Q f v) : RuleSafe Q (.branch c d t f) := by
  intro σ fr hσ hf ch v hv
  obtain ⟨b, bs, y, ys, -, hy, rfl⟩ := fire_branch hf
  have hQ := h y (hσ d y (by rw [hy]; simp))
  simp only [List.mem_append] at hv
  rcases hv with hv | hv
  · split at hv
    · rename_i hc; rw [hc.1]; simp only [List.mem_singleton] at hv; subst hv; exact hQ.1
    · cases hv
  · split at hv
    · rename_i hc; rw [hc.1]; simp only [List.mem_singleton] at hv; subst hv; exact hQ.2
    · cases hv

theorem mux_safe {s : Nat} {ds : List Nat} {o iw : Nat} (h : ∀ d ∈ ds, ∀ v, Q d v → Q o v) :
    RuleSafe Q (.mux s ds o iw) := by
  intro σ fr hσ hf ch v hv
  have hf' : muxF natVI s ds o iw σ = some fr := hf
  obtain ⟨w, ws, j, d, x, xs, -, -, hd, -, hx, rfl⟩ := muxF_some hf'
  simp only at hv
  split at hv
  · rename_i hc; subst hc
    simp only [List.mem_singleton] at hv; subst hv
    exact h d (List.mem_of_getElem? hd) v (hσ d v (by rw [hx]; simp))
  · cases hv

theorem cm_safe {i res idx k : Nat} (h : ∀ v, Q i v → Q res v) (hk : Q idx k) : RuleSafe Q (.cm i res idx k) := by
  intro σ fr hσ hf ch v hv
  obtain ⟨w, ws, out, hw, hg, rfl⟩ := fire1 (g := (Rule.cm i res idx k).out natVI) hf
  simp only [Rule.out, Option.some.injEq] at hg; subst hg
  simp only [List.mem_append] at hv
  rcases hv with hv | hv
  · split at hv
    · rename_i hc; subst hc
      simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hv; subst hv
      exact h v (hσ i v (by rw [hw]; simp))
    · cases hv
  · split at hv
    · rename_i hc; subst hc
      simp only [natVI, List.mem_singleton] at hv; subst hv; exact hk
    · cases hv

theorem sink_safe {i : Nat} : RuleSafe Q (.sink i) := by
  intro σ fr hσ hf ch v hv
  obtain ⟨w, ws, out, hw, hg, rfl⟩ := fire1 (g := (Rule.sink i).out natVI) hf
  simp only [Rule.out, Option.some.injEq] at hg; subst hg
  cases hv

end Safe

/-! ## Branch pairs -/

/-- A branch pair: `lF: fork e [d0, x]`, optionally `lA: comp [d0] d fA` (when `hasA`; otherwise `d0 = d`),
`lC: comp [x, k] c F`, `lK: fork c os` with `cb ∈ os`, `lB: branch cb d t f`. -/
structure Pair where
  lF : Nat
  lA : Nat
  lC : Nat
  lK : Nat
  lB : Nat
  e : Nat
  d0 : Nat
  d : Nat
  x : Nat
  c : Nat
  cb : Nat
  k : Nat
  t : Nat
  f : Nat
  os : List Nat
  hasA : Bool
  fA : E
  F : E

/-- What the data path does to a value between the fork and the branch. -/
def Pair.g (p : Pair) (v : Nat) : Nat := if p.hasA then p.fA.eval [v] else v

/-- The data side, against the list `W` of the in-flight values as they left the fork:
with `lA`, `d` holds the `g`-images of a prefix of `W` and `d0` the rest; without, `d` holds `W`. -/
def DataOK (p : Pair) (D D0 W : List Nat) : Prop :=
  if p.hasA then W.drop D.length = D0 ∧ (W.take D.length).map p.g = D else W = D

/-- The relational invariant of a pair, on the contents of its private channels. `W` lists the in-flight
values in fork order; the condition tokens (`cb` then `c`) pair with its prefix, the compares not yet done
(`x`) are its suffix, and every true condition token pairs with a value whose `g`-image satisfies `Q t`. -/
def PInv (Q : Nat → Nat → Prop) (p : Pair) (CB C X D D0 : List Nat) : Prop :=
  ∃ W : List Nat, (CB ++ C).length ≤ W.length ∧ W.drop (CB ++ C).length = X ∧ DataOK p D D0 W ∧
    ∀ (i b a : Nat), (CB ++ C)[i]? = some b → W[i]? = some a → b % 2 = 1 → Q p.t (p.g a)

def PairInv (Q : Nat → Nat → Prop) (p : Pair) (σ : Store Nat Nat) : Prop :=
  PInv Q p (σ p.cb) (σ p.c) (σ p.x) (σ p.d) (σ p.d0)

section PInvLemmas
variable {Q : Nat → Nat → Prop} {p : Pair}

theorem pinv_empty : PInv Q p [] [] [] [] [] := by
  refine ⟨[], by simp, by simp, ?_, by simp⟩
  unfold DataOK; split <;> simp

/-- `lF` fires, with `lA`. -/
theorem pinv_F_A (hA : p.hasA = true) {CB C X D D0 : List Nat} (v : Nat) (h : PInv Q p CB C X D D0) :
    PInv Q p CB C (X ++ [v]) D (D0 ++ [v]) := by
  obtain ⟨W, hle, hx, hd, hi⟩ := h
  simp only [DataOK, hA, ↓reduceIte] at hd
  obtain ⟨h1, h2⟩ := hd
  have hlen : D.length ≤ W.length := by
    have := congrArg List.length h2; simp only [List.length_map, List.length_take] at this; omega
  refine ⟨W ++ [v], by simp only [List.length_append, List.length_singleton] at hle ⊢; omega, by rw [List.drop_append_of_le_length hle, hx], ?_, ?_⟩
  · simp only [DataOK, hA, ↓reduceIte]
    exact ⟨by rw [List.drop_append_of_le_length hlen, h1], by rw [List.take_append_of_le_length hlen, h2]⟩
  · intro i b a hb ha hb1
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hb
    rw [List.getElem?_append_left (by omega)] at ha
    exact hi i b a hb ha hb1

/-- `lF` fires, without `lA` (`d0 = d`). -/
theorem pinv_F_noA (hA : p.hasA = false) {CB C X D D0 D0' : List Nat} (v : Nat) (h : PInv Q p CB C X D D0) :
    PInv Q p CB C (X ++ [v]) (D ++ [v]) D0' := by
  obtain ⟨W, hle, hx, hd, hi⟩ := h
  simp only [DataOK, hA, Bool.false_eq_true, ↓reduceIte] at hd
  refine ⟨W ++ [v], by simp only [List.length_append, List.length_singleton] at hle ⊢; omega, by rw [List.drop_append_of_le_length hle, hx], ?_, ?_⟩
  · simp only [DataOK, hA, Bool.false_eq_true, ↓reduceIte]; rw [hd]
  · intro i b a hb ha hb1
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hb
    rw [List.getElem?_append_left (by omega)] at ha
    exact hi i b a hb ha hb1

/-- `lA` fires. -/
theorem pinv_A (hA : p.hasA = true) {CB C X D D0 : List Nat} {a : Nat} (h : PInv Q p CB C X D (a :: D0)) :
    PInv Q p CB C X (D ++ [p.fA.eval [a]]) D0 := by
  obtain ⟨W, hle, hx, hd, hi⟩ := h
  simp only [DataOK, hA, ↓reduceIte] at hd
  obtain ⟨h1, h2⟩ := hd
  have hWa : W[D.length]? = some a := by
    have := congrArg (·[0]?) h1; simpa [List.getElem?_drop] using this
  refine ⟨W, hle, hx, ?_, hi⟩
  simp only [DataOK, hA, ↓reduceIte, List.length_append, List.length_singleton]
  refine ⟨?_, ?_⟩
  · rw [← List.drop_drop, h1]; rfl
  · rw [List.take_add_one, hWa]; simp [h2, Pair.g, hA]

/-- `lC` fires on `a` (and any `w` on `k`). -/
theorem pinv_C (hP : ∀ v w, p.F.eval [v, w] % 2 = 1 → Q p.t (p.g v)) {CB C X D D0 : List Nat} {a : Nat}
    (w : Nat) (h : PInv Q p CB C (a :: X) D D0) : PInv Q p CB (C ++ [p.F.eval [a, w]]) X D D0 := by
  obtain ⟨W, hle, hx, hd, hi⟩ := h
  have hlen := congrArg List.length hx
  simp only [List.length_drop, List.length_cons] at hlen
  have hWa : W[(CB ++ C).length]? = some a := by
    have := congrArg (·[0]?) hx; simpa [List.getElem?_drop] using this
  have e1 : CB ++ (C ++ [p.F.eval [a, w]]) = (CB ++ C) ++ [p.F.eval [a, w]] := by simp
  refine ⟨W, ?_, ?_, hd, ?_⟩
  · rw [e1]; simp only [List.length_append, List.length_singleton] at hlen ⊢; omega
  · rw [e1, List.length_append, List.length_singleton, ← List.drop_drop, hx]; rfl
  · rw [e1]
    intro i b a' hb ha hb1
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hb
    simp only [List.length_append, List.length_singleton] at hlt
    by_cases hi' : i < (CB ++ C).length
    · rw [List.getElem?_append_left hi'] at hb; exact hi i b a' hb ha hb1
    · have hi2 : i = (CB ++ C).length := by simp only [List.length_append] at hi' ⊢; omega
      subst hi2
      rw [List.getElem?_append_right (Nat.le_refl _)] at hb
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hb
      rw [hWa] at ha; cases ha; subst hb
      exact hP a w hb1

/-- `lK` fires: the condition token moves from `c` to `cb`. -/
theorem pinv_K {CB C X D D0 : List Nat} {b : Nat} (h : PInv Q p CB (b :: C) X D D0) :
    PInv Q p (CB ++ [b]) C X D D0 := by
  have e1 : CB ++ [b] ++ C = CB ++ b :: C := by simp
  unfold PInv; rw [e1]; exact h

/-- `lB` fires: a true condition pairs with a `Q t` value, and the rest is still paired. -/
theorem pinv_B {CB C X D D0 D0' : List Nat} {b y : Nat} (h : PInv Q p (b :: CB) C X (y :: D) D0)
    (h0 : p.hasA = true → D0' = D0) : (b % 2 = 1 → Q p.t y) ∧ PInv Q p CB C X D D0' := by
  obtain ⟨W, hle, hx, hd, hi⟩ := h
  have hW : ∃ a W', W = a :: W' ∧ y = p.g a ∧ DataOK p D D0' W' := by
    cases hA : p.hasA
    · simp only [DataOK, hA, Bool.false_eq_true, ↓reduceIte] at hd; subst hd
      refine ⟨y, D, rfl, by simp [Pair.g, hA], by simp [DataOK, hA]⟩
    · simp only [DataOK, hA, ↓reduceIte] at hd
      obtain ⟨h1, h2⟩ := hd
      cases W with
      | nil => simp at h2
      | cons a W' =>
        simp only [List.length_cons, List.take_succ_cons, List.map_cons, List.cons.injEq,
          List.drop_succ_cons] at h1 h2
        refine ⟨a, W', rfl, h2.1.symm, ?_⟩
        simp only [DataOK, hA, ↓reduceIte]; rw [h0 hA]; exact ⟨h1, h2.2⟩
  obtain ⟨a, W', rfl, hy, hd'⟩ := hW
  refine ⟨fun hb1 => hy ▸ hi 0 b a rfl rfl hb1, W', ?_, ?_, hd', ?_⟩
  · simp only [List.cons_append, List.length_cons, List.length_append] at hle ⊢; omega
  · simpa using hx
  · intro i b' a' hb ha hb1; exact hi (i + 1) b' a' (by simpa using hb) (by simpa using ha) hb1

end PInvLemmas

/-- The hypotheses on one pair in the graph `rs`. -/
structure PairOK (rs : List Rule) (Q : Nat → Nat → Prop) (p : Pair) : Prop where
  hF : rs[p.lF]? = some (.fork p.e [p.d0, p.x])
  hA : p.hasA = true → rs[p.lA]? = some (.comp [p.d0] p.d p.fA)
  hA0 : p.hasA = false → p.d0 = p.d
  hC : rs[p.lC]? = some (.comp [p.x, p.k] p.c p.F)
  hK : rs[p.lK]? = some (.fork p.c p.os)
  hcb : p.cb ∈ p.os
  hos : ∀ ch ∈ p.os, ch ≠ p.d0 ∧ ch ≠ p.d ∧ ch ≠ p.x ∧ ch ≠ p.c
  hB : rs[p.lB]? = some (.branch p.cb p.d p.t p.f)
  hnd : [p.e, p.d, p.x, p.c, p.cb, p.k, p.t, p.f].Nodup
  hnd0 : p.hasA = true → p.d0 ∉ [p.e, p.d, p.x, p.c, p.cb, p.k, p.t, p.f]
  /-- No other rule reads or writes the private channels `d0 d x c cb`. -/
  priv : ∀ l r, rs[l]? = some r → l ≠ p.lF → (p.hasA = true → l ≠ p.lA) → l ≠ p.lC → l ≠ p.lK → l ≠ p.lB →
    ∀ ch, ch ∈ r.insL ∨ ch ∈ r.outsL → ch ≠ p.d0 ∧ ch ≠ p.d ∧ ch ≠ p.x ∧ ch ≠ p.c ∧ ch ≠ p.cb
  /-- A true compare means the data value is good for the true side. -/
  hP : ∀ v w, p.F.eval [v, w] % 2 = 1 → Q p.t (p.g v)
  /-- The false side is unconstrained. -/
  hfalse : ∀ v, Q p.f v

set_option hygiene false in
macro "ns" : tactic => `(tactic| simp only [upd, applyF, popOf, List.mem_cons, List.not_mem_nil, or_false,
  hed, hex, hec, hecb, hek, het, hef, hdx, hdc, hdcb, hdk, hdt, hdf, hxc, hxcb, hxk, hxt, hxf, hccb, hck, hct, hcf,
  hcbk, hcbt, hcbf, hkt, hkf, htf, Ne.symm hed, Ne.symm hex, Ne.symm hec, Ne.symm hecb, Ne.symm hek, Ne.symm het,
  Ne.symm hef, Ne.symm hdx, Ne.symm hdc, Ne.symm hdcb, Ne.symm hdk, Ne.symm hdt, Ne.symm hdf, Ne.symm hxc,
  Ne.symm hxcb, Ne.symm hxk, Ne.symm hxt, Ne.symm hxf, Ne.symm hccb, Ne.symm hck, Ne.symm hct, Ne.symm hcf,
  Ne.symm hcbk, Ne.symm hcbt, Ne.symm hcbf, Ne.symm hkt, Ne.symm hkf, Ne.symm htf, ↓reduceIte, false_and,
  and_false, or_self, List.append_nil, List.nil_append, List.drop_zero, List.drop_succ_cons, true_or, or_true])

set_option hygiene false in
macro "ns0" : tactic => `(tactic| simp only [upd, applyF, popOf, List.mem_cons, List.not_mem_nil, or_false,
  h0e, h0d, h0x, h0c, h0cb, h0k, h0t, h0f, Ne.symm h0e, Ne.symm h0d, Ne.symm h0x, Ne.symm h0c, Ne.symm h0cb,
  Ne.symm h0k, Ne.symm h0t, Ne.symm h0f,
  hed, hex, hec, hecb, hek, het, hef, hdx, hdc, hdcb, hdk, hdt, hdf, hxc, hxcb, hxk, hxt, hxf, hccb, hck, hct, hcf,
  hcbk, hcbt, hcbf, hkt, hkf, htf, Ne.symm hed, Ne.symm hex, Ne.symm hec, Ne.symm hecb, Ne.symm hek, Ne.symm het,
  Ne.symm hef, Ne.symm hdx, Ne.symm hdc, Ne.symm hdcb, Ne.symm hdk, Ne.symm hdt, Ne.symm hdf, Ne.symm hxc,
  Ne.symm hxcb, Ne.symm hxk, Ne.symm hxt, Ne.symm hxf, Ne.symm hccb, Ne.symm hck, Ne.symm hct, Ne.symm hcf,
  Ne.symm hcbk, Ne.symm hcbt, Ne.symm hcbf, Ne.symm hkt, Ne.symm hkf, Ne.symm htf, ↓reduceIte, false_and,
  and_false, or_self, List.append_nil, List.nil_append, List.drop_zero, List.drop_succ_cons, true_or, or_true])

set_option hygiene false in
macro "getne" P:term : tactic => `(tactic| (
  have H := ($P).hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at H
  obtain ⟨⟨hed, hex, hec, hecb, hek, het, hef⟩, ⟨hdx, hdc, hdcb, hdk, hdt, hdf⟩, ⟨hxc, hxcb, hxk, hxt, hxf⟩,
    ⟨hccb, hck, hct, hcf⟩, ⟨hcbk, hcbt, hcbf⟩, ⟨hkt, hkf⟩, htf⟩ := H))

set_option hygiene false in
macro "getne0" P:term "," hA:term : tactic => `(tactic| (
  have H0 := ($P).hnd0 $hA
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at H0
  obtain ⟨h0e, h0d, h0x, h0c, h0cb, h0k, h0t, h0f⟩ := H0))

section Step
variable {rs : List Rule} {Q : Nat → Nat → Prop} {p : Pair}

/-- At the branch: a true condition token pushes a value good for the true side. -/
theorem pairInv_head {σ : Store Nat Nat} (hI : PairInv Q p σ) {b y : Nat} {bs ys : List Nat} (hb : σ p.cb = b :: bs)
    (hy : σ p.d = y :: ys) (hb1 : b % 2 = 1) : Q p.t y := by
  unfold PairInv at hI; rw [hb, hy] at hI
  exact (pinv_B (D0' := σ p.d0) hI (fun _ => rfl)).1 hb1

theorem pairInv_empty {σ : Store Nat Nat} (h : σ p.d0 = [] ∧ σ p.d = [] ∧ σ p.x = [] ∧ σ p.c = [] ∧ σ p.cb = []) :
    PairInv Q p σ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold PairInv; rw [h1, h2, h3, h4, h5]; exact pinv_empty

theorem pair_step (P : PairOK rs Q p) {σ σ1 : Store Nat Nat} {l : Nat}
    (h : step (graph rs) σ l = some σ1) (hI : PairInv Q p σ) : PairInv Q p σ1 := by
  getne P
  by_cases hlF : l = p.lF
  · subst hlF
    cases hA : p.hasA
    · have h0 := P.hA0 hA
      have hr := P.hF; rw [h0] at hr
      cases he : σ p.e with
      | nil => rw [step_fork2_none hr he] at h; cases h
      | cons v vs =>
        rw [step_fork2 hr hed hex hdx he] at h; cases h
        unfold PairInv at hI ⊢; rw [h0] at hI ⊢
        have := pinv_F_noA (D0' := σ p.d ++ [v]) hA v hI
        ns; exact this
    · getne0 P, hA
      cases he : σ p.e with
      | nil => rw [step_fork2_none P.hF he] at h; cases h
      | cons v vs =>
        rw [step_fork2 P.hF (Ne.symm h0e) hex h0x he] at h; cases h
        unfold PairInv at hI ⊢
        have := pinv_F_A hA v hI
        ns0; exact this
  by_cases hlA : p.hasA = true ∧ l = p.lA
  · obtain ⟨hA, rfl⟩ := hlA
    getne0 P, hA
    cases hd0 : σ p.d0 with
    | nil => rw [step_comp1_none (P.hA hA) hd0] at h; cases h
    | cons a rest =>
      rw [step_comp1 (P.hA hA) h0d hd0] at h; cases h
      unfold PairInv at hI ⊢; rw [hd0] at hI
      have := pinv_A hA hI
      ns0; exact this
  by_cases hlC : l = p.lC
  · subst hlC
    cases hx : σ p.x with
    | nil => rw [step_comp2_none P.hC (Or.inl hx)] at h; cases h
    | cons a xr =>
      cases hk : σ p.k with
      | nil => rw [step_comp2_none P.hC (Or.inr hk)] at h; cases h
      | cons w kr =>
        rw [step_comp2 P.hC hxk hxc (Ne.symm hck) hx hk] at h; cases h
        unfold PairInv at hI ⊢; rw [hx] at hI
        have := pinv_C P.hP w hI
        cases hA : p.hasA
        · rw [P.hA0 hA] at this ⊢; ns; exact this
        · getne0 P, hA; ns0; exact this
  by_cases hlK : l = p.lK
  · subst hlK
    obtain ⟨r, fr, hr, hf, rfl⟩ := step_some_rule h
    rw [P.hK, Option.some.injEq] at hr; subst hr
    obtain ⟨b, cr, hb, rfl⟩ := fire_fork hf
    have nd0 : p.d0 ∉ p.os := fun hm => (P.hos _ hm).1 rfl
    have nd : p.d ∉ p.os := fun hm => (P.hos _ hm).2.1 rfl
    have nx : p.x ∉ p.os := fun hm => (P.hos _ hm).2.2.1 rfl
    have nc : p.c ∉ p.os := fun hm => (P.hos _ hm).2.2.2 rfl
    unfold PairInv at hI ⊢; rw [hb] at hI
    have := pinv_K hI
    cases hA : p.hasA
    · rw [P.hA0 hA] at this ⊢; ns; simp only [nd, nx, nc, P.hcb, hb, ↓reduceIte, List.drop_zero, List.append_nil,
        List.drop_succ_cons]; exact this
    · getne0 P, hA; ns0; simp only [nd0, nd, nx, nc, P.hcb, hb, ↓reduceIte, List.drop_zero, List.append_nil,
        List.drop_succ_cons]; exact this
  by_cases hlB : l = p.lB
  · subst hlB
    obtain ⟨r, fr, hr, hf, rfl⟩ := step_some_rule h
    rw [P.hB, Option.some.injEq] at hr; subst hr
    obtain ⟨b, bs, y, ys, hb, hy, rfl⟩ := fire_branch hf
    unfold PairInv at hI ⊢; rw [hb, hy] at hI
    cases hA : p.hasA
    · have h0 := P.hA0 hA
      rw [h0] at hI ⊢
      have := (pinv_B (D0' := ys) hI (fun h' => by rw [hA] at h'; cases h')).2
      ns; simp only [hb, hy, List.drop_zero, List.drop_succ_cons]; exact this
    · getne0 P, hA
      have := (pinv_B (D0' := σ p.d0) hI (fun _ => rfl)).2
      ns0; simp only [hb, hy, List.drop_zero, List.drop_succ_cons]; exact this
  · obtain ⟨r, fr, hr, hf, rfl⟩ := step_some_rule h
    have hpv := P.priv l r hr hlF (fun hA e => hlA ⟨hA, e⟩) hlC hlK hlB
    have keep : ∀ ch, (∀ c', c' ∈ r.insL ∨ c' ∈ r.outsL → c' ≠ ch) → applyF σ fr ch = σ ch := fun ch hch =>
      applyF_keep hf (fun hm => hch ch (Or.inl hm) rfl) (fun hm => hch ch (Or.inr hm) rfl)
    unfold PairInv at hI ⊢
    rw [keep p.cb (fun c' hc => (hpv c' hc).2.2.2.2), keep p.c (fun c' hc => (hpv c' hc).2.2.2.1),
      keep p.x (fun c' hc => (hpv c' hc).2.2.1), keep p.d (fun c' hc => (hpv c' hc).2.1),
      keep p.d0 (fun c' hc => (hpv c' hc).1)]
    exact hI
end Step

/-! ## The invariant along every run -/

section Main
variable {rs : List Rule} {Q : Nat → Nat → Prop} {ps : List Pair}

/-- The channel invariant and every pair's relational invariant. -/
def AllInv (Q : Nat → Nat → Prop) (ps : List Pair) (σ : Store Nat Nat) : Prop :=
  SInv Q σ ∧ ∀ p ∈ ps, PairInv Q p σ

theorem sinv_step (hsafe : ∀ l r, rs[l]? = some r → (∀ p ∈ ps, l ≠ p.lB) → RuleSafe Q r)
    (hps : ∀ p ∈ ps, PairOK rs Q p) {σ σ1 : Store Nat Nat} {l : Nat} (h : step (graph rs) σ l = some σ1)
    (hI : AllInv Q ps σ) : SInv Q σ1 := by
  obtain ⟨r, fr, hr, hf, rfl⟩ := step_some_rule h
  by_cases hB : ∃ p ∈ ps, l = p.lB
  · obtain ⟨p, hp, rfl⟩ := hB
    have P := hps p hp
    rw [P.hB, Option.some.injEq] at hr; subst hr
    obtain ⟨b, bs, y, ys, hb, hy, rfl⟩ := fire_branch hf
    refine sinv_apply hI.1 fun ch v hv => ?_
    simp only [List.mem_append] at hv
    rcases hv with hv | hv
    · split at hv
      · rename_i hc; rw [hc.1]; simp only [List.mem_singleton] at hv; subst hv
        exact pairInv_head (hI.2 p hp) hb hy hc.2
      · cases hv
    · split at hv
      · rename_i hc; rw [hc.1]; simp only [List.mem_singleton] at hv; subst hv; exact P.hfalse v
      · cases hv
  · exact sinv_apply hI.1 (hsafe l r hr (fun p hp e => hB ⟨p, hp, e⟩) σ fr hI.1 hf)

theorem allInv_step (hsafe : ∀ l r, rs[l]? = some r → (∀ p ∈ ps, l ≠ p.lB) → RuleSafe Q r)
    (hps : ∀ p ∈ ps, PairOK rs Q p) {σ σ1 : Store Nat Nat} {l : Nat} (h : step (graph rs) σ l = some σ1)
    (hI : AllInv Q ps σ) : AllInv Q ps σ1 :=
  ⟨sinv_step hsafe hps h hI, fun p hp => pair_step (hps p hp) h (hI.2 p hp)⟩

theorem allInv_run (hsafe : ∀ l r, rs[l]? = some r → (∀ p ∈ ps, l ≠ p.lB) → RuleSafe Q r)
    (hps : ∀ p ∈ ps, PairOK rs Q p) {σ t : Store Nat Nat} {n : Nat} (hr : Run (step (graph rs)) σ n t) :
    AllInv Q ps σ → AllInv Q ps t := by
  induction hr with
  | refl => exact id
  | cons l hl _ ih => exact fun hI => ih (allInv_step hsafe hps hl hI)

/-- **Main theorem.** Every rule except the pairs' branches is `Q`-safe, every pair satisfies `PairOK`
(the true side of its branch is guarded by its compare, the false side is unconstrained); start from a
`Q`-store whose pairs' private channels are empty. Then every reachable store is a `Q`-store and every pair's
relational invariant holds there. -/
theorem chan_inv (hsafe : ∀ l r, rs[l]? = some r → (∀ p ∈ ps, l ≠ p.lB) → RuleSafe Q r)
    (hps : ∀ p ∈ ps, PairOK rs Q p) {σ0 : Store Nat Nat} (h0 : SInv Q σ0)
    (hemp : ∀ p ∈ ps, σ0 p.d0 = [] ∧ σ0 p.d = [] ∧ σ0 p.x = [] ∧ σ0 p.c = [] ∧ σ0 p.cb = [])
    {n : Nat} {t : Store Nat Nat} (hr : Run (step (graph rs)) σ0 n t) :
    SInv Q t ∧ ∀ p ∈ ps, PairInv Q p t :=
  allInv_run hsafe hps hr ⟨h0, fun p hp => pairInv_empty (hemp p hp)⟩

/-- Corollary: at any reachable store, when a pair's branch fires to the true side, the value it pushes
satisfies `Q t` (read off the heads of `cb` and `d`). -/
theorem chan_inv_true (hsafe : ∀ l r, rs[l]? = some r → (∀ p ∈ ps, l ≠ p.lB) → RuleSafe Q r)
    (hps : ∀ p ∈ ps, PairOK rs Q p) {σ0 : Store Nat Nat} (h0 : SInv Q σ0)
    (hemp : ∀ p ∈ ps, σ0 p.d0 = [] ∧ σ0 p.d = [] ∧ σ0 p.x = [] ∧ σ0 p.c = [] ∧ σ0 p.cb = [])
    {n : Nat} {t : Store Nat Nat} (hr : Run (step (graph rs)) σ0 n t) {p : Pair} (hp : p ∈ ps)
    {b y : Nat} {bs ys : List Nat} (hb : t p.cb = b :: bs) (hy : t p.d = y :: ys) (hb1 : b % 2 = 1) :
    Q p.t y :=
  pairInv_head ((chan_inv hsafe hps h0 hemp hr).2 p hp) hb hy hb1

end Main

end Formal.Rewrite.ChanInv
