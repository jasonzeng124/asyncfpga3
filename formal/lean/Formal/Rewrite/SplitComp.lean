import Formal.Rewrite.IncCmp2

/-!
# Formal.Rewrite.SplitComp — splitting a two-input compute region in two preserves every complete run (shard A, 2026-11-18)

**Problem, plainly.** bdc fuses at most `BDC_MAX_FUSE_NODES` (4) ops into one region. A computation `z = F(x, y)` with
more ops is emitted as `fork y -> (y1, y2) ; w = F1(x, y1) ; z = F2(y2, w)`. dfimport imports what bdc emits, so a
proof about the one-region graph must be carried to the split one. Same function, whatever surrounds it?

**Proved** (`split_forward`, `split_backward`): for ANY imported graph `rs` holding `comp [x, y] z F` at label `p`,
and `rs'` equal except `fork y [y1, y2]` at `p` and `comp [x, y1] w F1`, `comp [y2, w] z F2` at two labels unused in
`rs`, with `y1 y2 w` fresh, nothing else reading `x y y1 y2 w` or producing `y1 y2 w z`, and
`∀ a b, F2(b, F1(a, b)) = F(a, b)`: from any store with `y1 y2 w` empty, every complete run of either graph is matched
by a complete run of the other ending in the same store outside `x y y1 y2 w`.

**Not covered:** token level only.
-/

namespace Formal.Rewrite.IncCmp

open Formal.Net.Kahn Formal.Net.GcdHw

theorem lft_cont : ∀ (X Y A B : List Nat), lft (X ++ A) (Y ++ B) = lft ((lft X Y).1 ++ A) ((lft X Y).2 ++ B)
  | [], Y, A, B => by simp
  | a :: X, [], A, B => by simp
  | a :: X, w :: Y, A, B => by simp only [List.cons_append, lft_cons]; exact lft_cont X Y A B

theorem zw_cont (f : Nat → Nat → Nat) : ∀ (X Y A B : List Nat),
    List.zipWith f (X ++ A) (Y ++ B) = List.zipWith f X Y ++ List.zipWith f ((lft X Y).1 ++ A) ((lft X Y).2 ++ B)
  | [], Y, A, B => by simp
  | a :: X, [], A, B => by simp
  | a :: X, w :: Y, A, B => by
    simp only [List.cons_append, List.zipWith_cons_cons, lft_cons, zw_cont f X Y A B]

theorem lft_zip (g : Nat → Nat → Nat) : ∀ (X Y : List Nat), lft Y (List.zipWith g X Y) = ((lft X Y).2, [])
  | [], Y => by simp
  | a :: X, [] => by simp
  | a :: X, w :: Y => by simp only [List.zipWith_cons_cons, lft_cons]; exact lft_zip g X Y

theorem zw_zip (f2 : Nat → Nat → Nat) (g : Nat → Nat → Nat) : ∀ (X Y : List Nat),
    List.zipWith f2 Y (List.zipWith g X Y) = List.zipWith (fun a b => f2 b (g a b)) X Y
  | [], Y => by simp
  | a :: X, [] => by simp
  | a :: X, w :: Y => by simp only [List.zipWith_cons_cons, zw_zip f2 g X Y]

theorem zw_app_eq (f : Nat → Nat → Nat) : ∀ (X Y A B : List Nat), X.length = Y.length →
    List.zipWith f (X ++ A) (Y ++ B) = List.zipWith f X Y ++ List.zipWith f A B
  | [], [], A, B, _ => by simp
  | a :: X, w :: Y, A, B, h => by
    simp only [List.cons_append, List.zipWith_cons_cons, List.length_cons, Nat.add_right_cancel_iff] at h ⊢
    rw [zw_app_eq f X Y A B h]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem lft_app_eq : ∀ (X Y A B : List Nat), X.length = Y.length → lft (X ++ A) (Y ++ B) = lft A B
  | [], [], A, B, _ => by simp
  | a :: X, w :: Y, A, B, h => by
    simp only [List.cons_append, lft_cons, List.length_cons, Nat.add_right_cancel_iff] at h ⊢
    exact lft_app_eq X Y A B h
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

section Split

variable {rs rs' : List Rule} {p q r x y y1 y2 w z : Nat} {F F1 F2 : E}

structure PatS (rs rs' : List Rule) (p q r x y y1 y2 w z : Nat) (F F1 F2 : E) : Prop where
  hp : rs[p]? = some (.comp [x, y] z F)
  hp' : rs'[p]? = some (.fork y [y1, y2])
  hq : rs[q]? = none
  hq' : rs'[q]? = some (.comp [x, y1] w F1)
  hr : rs[r]? = none
  hr' : rs'[r]? = some (.comp [y2, w] z F2)
  hsame : ∀ l, l ≠ p → l ≠ q → l ≠ r → rs'[l]? = rs[l]?
  hins : ∀ l ru, l ≠ p → rs[l]? = some ru → ∀ ch ∈ ru.insL, ch ≠ x ∧ ch ≠ y ∧ ch ≠ y1 ∧ ch ≠ y2 ∧ ch ≠ w
  houts : ∀ l ru, l ≠ p → rs[l]? = some ru → ∀ ch ∈ ru.outsL, ch ≠ y1 ∧ ch ≠ y2 ∧ ch ≠ w ∧ ch ≠ z
  hnd : [x, y, y1, y2, w, z].Nodup
  hH : ∀ a b, F2.eval [b, F1.eval [a, b]] = F.eval [a, b]

structure Ne6 (x y y1 y2 w z : Nat) : Prop where
  xy : x ≠ y
  xy1 : x ≠ y1
  xy2 : x ≠ y2
  xw : x ≠ w
  xz : x ≠ z
  yy1 : y ≠ y1
  yy2 : y ≠ y2
  yw : y ≠ w
  yz : y ≠ z
  y1y2 : y1 ≠ y2
  y1w : y1 ≠ w
  y1z : y1 ≠ z
  y2w : y2 ≠ w
  y2z : y2 ≠ z
  wz : w ≠ z

theorem ne6 (h : [x, y, y1, y2, w, z].Nodup) : Ne6 x y y1 y2 w z := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false] at h
  constructor <;> intro hh <;> subst hh <;> simp_all

set_option hygiene false in
macro "ssimp" : tactic => `(tactic| simp only [upd, M.xy, M.xy1, M.xy2, M.xw, M.xz, M.yy1, M.yy2, M.yw, M.yz,
  M.y1y2, M.y1w, M.y1z, M.y2w, M.y2z, M.wz, M.xy.symm, M.xy1.symm, M.xy2.symm, M.xw.symm, M.xz.symm, M.yy1.symm,
  M.yy2.symm, M.yw.symm, M.yz.symm, M.y1y2.symm, M.y1w.symm, M.y1z.symm, M.y2w.symm, M.y2z.symm, M.wz.symm,
  ↓reduceIte, if_true, if_false])

def RelS (x y y1 y2 w z : Nat) (F F1 : E) (σ σ' : Store Nat Nat) : Prop :=
  (∀ ch, ch ≠ x → ch ≠ y → ch ≠ y1 → ch ≠ y2 → ch ≠ w → ch ≠ z → σ' ch = σ ch) ∧
  σ y1 = [] ∧ σ y2 = [] ∧ σ w = [] ∧
  ∃ Xw Yw : List Nat, Xw.length = Yw.length ∧
    σ' w = List.zipWith (fun a b => F1.eval [a, b]) Xw Yw ∧ σ' y2 = Yw ++ σ' y1 ∧
    σ z ++ List.zipWith (fun a b => F.eval [a, b]) (σ x) (σ y) =
      σ' z ++ List.zipWith (fun a b => F.eval [a, b]) Xw Yw ++
        List.zipWith (fun a b => F.eval [a, b]) (σ' x) (σ' y1 ++ σ' y) ∧
    lft (σ x) (σ y) = lft (σ' x) (σ' y1 ++ σ' y)

/-- The split graph's flush: fork every `y`, pair `x` with `y1`, pair `y2` with `w`. -/
theorem flushSB (P : PatS rs rs' p q r x y y1 y2 w z F F1 F2) (σ : Store Nat Nat) (Xw Yw : List Nat)
    (hl : Xw.length = Yw.length) (hw : σ w = List.zipWith (fun a b => F1.eval [a, b]) Xw Yw)
    (h2 : σ y2 = Yw ++ σ y1) :
    ∃ τ n, Run (step (graph rs')) σ n τ ∧ τ y = [] ∧ τ w = [] ∧
      τ x = (lft (σ x) (σ y1 ++ σ y)).1 ∧ τ y1 = (lft (σ x) (σ y1 ++ σ y)).2 ∧
      τ y2 = (lft (σ x) (σ y1 ++ σ y)).2 ∧
      τ z = σ z ++ List.zipWith (fun a b => F.eval [a, b]) Xw Yw ++
        List.zipWith (fun a b => F.eval [a, b]) (σ x) (σ y1 ++ σ y) ∧
      ∀ ch, ch ≠ x → ch ≠ y → ch ≠ y1 → ch ≠ y2 → ch ≠ w → ch ≠ z → τ ch = σ ch := by
  have M := ne6 P.hnd
  obtain ⟨n1, r1⟩ := drain_fork2 P.hp' M.yy1 M.yy2 M.y1y2 (σ y) σ rfl
  let σ1 := upd (upd (upd σ y []) y1 (σ y1 ++ σ y)) y2 (σ y2 ++ σ y)
  obtain ⟨n2, r2⟩ := drain_comp2 P.hq' M.xy1 M.xw M.y1w (σ1 x) (σ1 y1) σ1 rfl rfl
  let σ2 := upd (upd (upd σ1 x (lft (σ1 x) (σ1 y1)).1) y1 (lft (σ1 x) (σ1 y1)).2) w
    (σ1 w ++ List.zipWith (fun a b => F1.eval [a, b]) (σ1 x) (σ1 y1))
  obtain ⟨n3, r3⟩ := drain_comp2 P.hr' M.y2w M.y2z M.wz (σ2 y2) (σ2 w) σ2 rfl rfl
  refine ⟨_, _, run_trans r1 (run_trans r2 r3), ?_⟩
  have e1 : σ2 y2 = Yw ++ (σ y1 ++ σ y) := by simp only [σ2, σ1]; ssimp; rw [h2, List.append_assoc]
  have e2 : σ2 w = List.zipWith (fun a b => F1.eval [a, b]) Xw Yw ++
      List.zipWith (fun a b => F1.eval [a, b]) (σ x) (σ y1 ++ σ y) := by simp only [σ2, σ1]; ssimp; rw [hw]
  have hl2 : (List.zipWith (fun a b => F1.eval [a, b]) Xw Yw).length = Yw.length := by simp [hl]
  have eL : lft (σ2 y2) (σ2 w) = ((lft (σ x) (σ y1 ++ σ y)).2, []) := by
    rw [e1, e2, lft_app_eq _ _ _ _ hl2.symm, lft_zip]
  have eZ : List.zipWith (fun a b => F2.eval [a, b]) (σ2 y2) (σ2 w) =
      List.zipWith (fun a b => F.eval [a, b]) Xw Yw ++
        List.zipWith (fun a b => F.eval [a, b]) (σ x) (σ y1 ++ σ y) := by
    rw [e1, e2, zw_app_eq _ _ _ _ _ hl2.symm, zw_zip, zw_zip]
    simp only [P.hH]
  rw [eL, eZ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [σ2, σ1]; ssimp
  · ssimp
  · simp only [σ2, σ1]; ssimp
  · simp only [σ2, σ1]; ssimp
  · ssimp
  · simp only [σ2, σ1]; ssimp; simp [List.append_assoc]
  · intro ch k1 k2 k3 k4 k5 k6; simp only [σ2, σ1]; simp [upd, k1, k2, k3, k4, k5, k6]

/-- The one-region graph's flush: pair `x` with `y`. -/
theorem flushSA (P : PatS rs rs' p q r x y y1 y2 w z F F1 F2) (σ : Store Nat Nat) :
    ∃ τ n, Run (step (graph rs)) σ n τ ∧ τ x = (lft (σ x) (σ y)).1 ∧ τ y = (lft (σ x) (σ y)).2 ∧
      τ z = σ z ++ List.zipWith (fun a b => F.eval [a, b]) (σ x) (σ y) ∧
      ∀ ch, ch ≠ x → ch ≠ y → ch ≠ z → τ ch = σ ch := by
  have M := ne6 P.hnd
  obtain ⟨n1, r1⟩ := drain_comp2 P.hp M.xy M.xz M.yz (σ x) (σ y) σ rfl rfl
  refine ⟨_, _, r1, ?_, ?_, ?_, ?_⟩
  · ssimp
  · ssimp
  · ssimp
  · intro ch k1 k2 k3; simp [upd, k1, k2, k3]

theorem s_nin {r0 : Rule} {l : Nat} (P : PatS rs rs' p q r x y y1 y2 w z F F1 F2) (lp : l ≠ p)
    (hr0 : rs[l]? = some r0) : ∀ ch, (ch = x ∨ ch = y ∨ ch = y1 ∨ ch = y2 ∨ ch = w) → ch ∉ r0.insL := by
  intro ch hc hm; obtain ⟨k1, k2, k3, k4, k5⟩ := P.hins l r0 lp hr0 ch hm
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp_all

theorem s_nout {r0 : Rule} {l : Nat} (P : PatS rs rs' p q r x y y1 y2 w z F F1 F2) (lp : l ≠ p)
    (hr0 : rs[l]? = some r0) : ∀ ch, (ch = y1 ∨ ch = y2 ∨ ch = w ∨ ch = z) → ch ∉ r0.outsL := by
  intro ch hc hm; obtain ⟨k1, k2, k3, k4⟩ := P.houts l r0 lp hr0 ch hm
  rcases hc with rfl | rfl | rfl | rfl <;> simp_all

theorem s_push {r0 : Rule} {fr : Fire Nat Nat} {ρ : Store Nat Nat} (hf : r0.fire natVI ρ = some fr) {ch : Nat}
    (hi : ch ∉ r0.insL) : applyF ρ fr ch = ρ ch ++ fr.2 ch := by
  have := (r0.node natVI).pop_ins ρ fr ch hf hi
  simp [applyF, this]

theorem fwd_stepS (P : PatS rs rs' p q r x y y1 y2 w z F F1 F2) :
    ∀ σ σ' l σ1, RelS x y y1 y2 w z F F1 σ σ' → step (graph rs) σ l = some σ1 →
      ∃ σ1' n, Run (step (graph rs')) σ' n σ1' ∧ RelS x y y1 y2 w z F F1 σ1 σ1' := by
  have M := ne6 P.hnd
  intro σ σ' l σ1 ⟨hR, h1, h2, h3, Xw, Yw, hl, hw, hy2, hD, hE⟩ hst
  by_cases lp : l = p
  · subst lp
    cases hx : σ x with
    | nil => rw [step_comp2_none P.hp (Or.inl hx)] at hst; cases hst
    | cons a as =>
      cases hy : σ y with
      | nil => rw [step_comp2_none P.hp (Or.inr hy)] at hst; cases hst
      | cons b bs =>
        rw [step_comp2 P.hp M.xy M.xz M.yz hx hy] at hst; cases hst
        refine ⟨σ', 0, Run.refl _, ?_, ?_, ?_, ?_, Xw, Yw, hl, hw, hy2, ?_, ?_⟩
        · intro ch k1 k2 k3 k4 k5 k6; simp [upd, k1, k2, k6, hR ch k1 k2 k3 k4 k5 k6]
        · ssimp; exact h1
        · ssimp; exact h2
        · ssimp; exact h3
        · ssimp; rw [← hD, hx, hy]; simp
        · ssimp; rw [← hE, hx, hy]; rfl
  obtain ⟨r0, fr, hr0, hf, rfl⟩ := step_some_rule hst
  have lq : l ≠ q := by intro h; subst h; rw [P.hq] at hr0; cases hr0
  have lr : l ≠ r := by intro h; subst h; rw [P.hr] at hr0; cases hr0
  have nin := s_nin P lp hr0
  have nout := s_nout P lp hr0
  obtain ⟨τ, n, hrun, ty, tw, tx, ty1, ty2, tz, tR⟩ := flushSB P σ' Xw Yw hl hw hy2
  have hfτ : r0.fire natVI τ = some fr := by
    refine fire_mono hf ?_
    intro ch hch
    by_cases kz : ch = z
    · subst kz; exact ⟨_, by rw [tz, ← hD]⟩
    · have := nin ch
      have k1 : ch ≠ x := fun h => this (Or.inl h) hch
      have k2 : ch ≠ y := fun h => this (Or.inr (Or.inl h)) hch
      have k3 : ch ≠ y1 := fun h => this (Or.inr (Or.inr (Or.inl h))) hch
      have k4 : ch ≠ y2 := fun h => this (Or.inr (Or.inr (Or.inr (Or.inl h)))) hch
      have k5 : ch ≠ w := fun h => this (Or.inr (Or.inr (Or.inr (Or.inr h)))) hch
      exact ⟨[], by rw [List.append_nil, tR ch k1 k2 k3 k4 k5 kz, hR ch k1 k2 k3 k4 k5 kz]⟩
  have hst' : step (graph rs') τ l = some (applyF τ fr) := by
    rw [step_graph (by rw [P.hsame l lp lq lr]; exact hr0), hfτ]; rfl
  have kk := fire_le hf z
  refine ⟨_, n + 1, run_trans hrun (run_one hst'), ?_, ?_, ?_, ?_, [], [], rfl, ?_, ?_, ?_, ?_⟩
  · intro ch k1 k2 k3 k4 k5 k6
    simp only [applyF]; rw [tR ch k1 k2 k3 k4 k5 k6, hR ch k1 k2 k3 k4 k5 k6]
  · rw [applyF_keep hf (nin y1 (by simp)) (nout y1 (by simp)), h1]
  · rw [applyF_keep hf (nin y2 (by simp)) (nout y2 (by simp)), h2]
  · rw [applyF_keep hf (nin w (by simp)) (nout w (by simp)), h3]
  · rw [applyF_keep hfτ (nin w (by simp)) (nout w (by simp)), tw]; rfl
  · rw [applyF_keep hfτ (nin y2 (by simp)) (nout y2 (by simp)), applyF_keep hfτ (nin y1 (by simp))
      (nout y1 (by simp)), ty1, ty2]; rfl
  · rw [applyF_noout hf (nout z (by simp)), applyF_noout hfτ (nout z (by simp)), s_push hf (nin x (by simp)),
      s_push hf (nin y (by simp)), s_push hfτ (nin x (by simp)), s_push hfτ (nin y (by simp)),
      applyF_keep hfτ (nin y1 (by simp)) (nout y1 (by simp)), tx, ty1, ty, tz, ← hD, zw_cont, hE,
      List.drop_append_of_le_length kk]
    simp
  · rw [s_push hf (nin x (by simp)), s_push hf (nin y (by simp)), s_push hfτ (nin x (by simp)),
      s_push hfτ (nin y (by simp)), applyF_keep hfτ (nin y1 (by simp)) (nout y1 (by simp)), tx, ty1, ty,
      lft_cont, hE]
    simp

theorem fwd_termS (P : PatS rs rs' p q r x y y1 y2 w z F F1 F2) :
    ∀ t σ', RelS x y y1 y2 w z F F1 t σ' → Terminal (step (graph rs)) t →
      ∃ τ n, Run (step (graph rs')) σ' n τ ∧ Terminal (step (graph rs')) τ ∧
        ∀ ch, ch ≠ x → ch ≠ y → ch ≠ y1 → ch ≠ y2 → ch ≠ w → τ ch = t ch := by
  have M := ne6 P.hnd
  intro t σ' ⟨hR, h1, h2, h3, Xw, Yw, hl, hw, hy2, hD, hE⟩ ht
  have tp := term_comp2 P.hp M.xy M.xz M.yz ht
  obtain ⟨τ, n, hrun, ty, tw, tx, ty1, ty2, tz, tR⟩ := flushSB P σ' Xw Yw hl hw hy2
  rw [lft_of_empty tp] at hE
  rw [zw_of_empty _ tp, List.append_nil] at hD
  have agree : ∀ ch, ch ≠ x → ch ≠ y → ch ≠ y1 → ch ≠ y2 → ch ≠ w → τ ch = t ch := by
    intro ch k1 k2 k3 k4 k5
    by_cases k6 : ch = z
    · subst k6; rw [tz, ← hD]
    · rw [tR ch k1 k2 k3 k4 k5 k6, hR ch k1 k2 k3 k4 k5 k6]
  refine ⟨τ, n, hrun, ?_, agree⟩
  intro l
  by_cases lp : l = p
  · subst lp; exact step_fork2_none P.hp' ty
  by_cases lq : l = q
  · subst lq
    refine step_comp2_none P.hq' ?_
    rw [tx, ty1, ← hE]; exact tp
  by_cases lr : l = r
  · subst lr; exact step_comp2_none P.hr' (Or.inr tw)
  refine other_none (P.hsame l lp lq lr) (ht l) ?_
  intro r0 hr0 ch hch
  have := s_nin P lp hr0 ch
  exact agree ch (fun h => this (Or.inl h) hch) (fun h => this (Or.inr (Or.inl h)) hch)
    (fun h => this (Or.inr (Or.inr (Or.inl h))) hch) (fun h => this (Or.inr (Or.inr (Or.inr (Or.inl h)))) hch)
    (fun h => this (Or.inr (Or.inr (Or.inr (Or.inr h)))) hch)

theorem bwd_stepS (P : PatS rs rs' p q r x y y1 y2 w z F F1 F2) :
    ∀ σ' σ l σ1', RelS x y y1 y2 w z F F1 σ σ' → step (graph rs') σ' l = some σ1' →
      ∃ σ1 n, Run (step (graph rs)) σ n σ1 ∧ RelS x y y1 y2 w z F F1 σ1 σ1' := by
  have M := ne6 P.hnd
  intro σ' σ l σ1' ⟨hR, h1, h2, h3, Xw, Yw, hl, hw, hy2, hD, hE⟩ hst
  by_cases lp : l = p
  · subst lp
    cases hy : σ' y with
    | nil => rw [step_fork2_none P.hp' hy] at hst; cases hst
    | cons b bs =>
      rw [step_fork2 P.hp' M.yy1 M.yy2 M.y1y2 hy] at hst; cases hst
      refine ⟨σ, 0, Run.refl _, ?_, h1, h2, h3, Xw, Yw, hl, ?_, ?_, ?_, ?_⟩
      · intro ch k1 k2 k3 k4 k5 k6; simp [upd, k2, k3, k4, hR ch k1 k2 k3 k4 k5 k6]
      · ssimp; exact hw
      · ssimp; rw [hy2]; simp
      · ssimp; rw [hD, hy]; simp
      · ssimp; rw [hE, hy]; simp
  by_cases lq : l = q
  · subst lq
    cases hx : σ' x with
    | nil => rw [step_comp2_none P.hq' (Or.inl hx)] at hst; cases hst
    | cons a as =>
      cases hy1 : σ' y1 with
      | nil => rw [step_comp2_none P.hq' (Or.inr hy1)] at hst; cases hst
      | cons b bs =>
        rw [step_comp2 P.hq' M.xy1 M.xw M.y1w hx hy1] at hst; cases hst
        refine ⟨σ, 0, Run.refl _, ?_, h1, h2, h3, Xw ++ [a], Yw ++ [b], by simp [hl], ?_, ?_, ?_, ?_⟩
        · intro ch k1 k2 k3 k4 k5 k6; simp [upd, k1, k3, k5, hR ch k1 k2 k3 k4 k5 k6]
        · ssimp; rw [hw, zw_app_eq _ _ _ _ _ hl]; rfl
        · ssimp; rw [hy2, hy1]; simp
        · ssimp; rw [hD, hx, hy1, zw_app_eq _ _ _ _ _ hl]; simp
        · ssimp; rw [hE, hx, hy1]; rfl
  by_cases lr : l = r
  · subst lr
    cases hy2' : σ' y2 with
    | nil => rw [step_comp2_none P.hr' (Or.inl hy2')] at hst; cases hst
    | cons b bs =>
      cases hw' : σ' w with
      | nil => rw [step_comp2_none P.hr' (Or.inr hw')] at hst; cases hst
      | cons cc cs =>
        rw [step_comp2 P.hr' M.y2w M.y2z M.wz hy2' hw'] at hst; cases hst
        cases Xw with
        | nil => rw [hw] at hw'; simp at hw'
        | cons a Xw' =>
          cases Yw with
          | nil => simp at hl
          | cons b' Yw' =>
            simp only [List.cons_append, hy2', List.cons.injEq] at hy2
            obtain ⟨rfl, hbs⟩ := hy2
            rw [hw] at hw'
            simp only [List.zipWith_cons_cons, List.cons.injEq] at hw'
            obtain ⟨hc, hcs⟩ := hw'
            simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
            refine ⟨σ, 0, Run.refl _, ?_, h1, h2, h3, Xw', Yw', hl, ?_, ?_, ?_, ?_⟩
            · intro ch k1 k2 k3 k4 k5 k6; simp [upd, k4, k5, k6, hR ch k1 k2 k3 k4 k5 k6]
            · ssimp; exact hcs.symm
            · ssimp; exact hbs
            · ssimp; rw [hD, ← hc, P.hH]; simp
            · ssimp; exact hE
  obtain ⟨r0, fr, hr', hf, rfl⟩ := step_some_rule hst
  have hr0 : rs[l]? = some r0 := by rw [← P.hsame l lp lq lr]; exact hr'
  have nin := s_nin P lp hr0
  have nout := s_nout P lp hr0
  obtain ⟨τ, n, hrun, tx, ty, tz, tR⟩ := flushSA P σ
  have hfτ : r0.fire natVI τ = some fr := by
    refine fire_mono hf ?_
    intro ch hch
    by_cases kz : ch = z
    · subst kz; exact ⟨_, by rw [tz, hD, List.append_assoc]⟩
    · have := nin ch
      have k1 : ch ≠ x := fun h => this (Or.inl h) hch
      have k2 : ch ≠ y := fun h => this (Or.inr (Or.inl h)) hch
      have k3 : ch ≠ y1 := fun h => this (Or.inr (Or.inr (Or.inl h))) hch
      have k4 : ch ≠ y2 := fun h => this (Or.inr (Or.inr (Or.inr (Or.inl h)))) hch
      have k5 : ch ≠ w := fun h => this (Or.inr (Or.inr (Or.inr (Or.inr h)))) hch
      exact ⟨[], by rw [List.append_nil, tR ch k1 k2 kz, hR ch k1 k2 k3 k4 k5 kz]⟩
  have hst' : step (graph rs) τ l = some (applyF τ fr) := by
    rw [step_graph hr0, hfτ]; rfl
  have kk := fire_le hf z
  refine ⟨_, n + 1, run_trans hrun (run_one hst'), ?_, ?_, ?_, ?_, Xw, Yw, hl, ?_, ?_, ?_, ?_⟩
  · intro ch k1 k2 k3 k4 k5 k6
    simp only [applyF]; rw [tR ch k1 k2 k6, hR ch k1 k2 k3 k4 k5 k6]
  · rw [applyF_keep hfτ (nin y1 (by simp)) (nout y1 (by simp)), tR y1 M.xy1.symm M.yy1.symm M.y1z, h1]
  · rw [applyF_keep hfτ (nin y2 (by simp)) (nout y2 (by simp)), tR y2 M.xy2.symm M.yy2.symm M.y2z, h2]
  · rw [applyF_keep hfτ (nin w (by simp)) (nout w (by simp)), tR w M.xw.symm M.yw.symm M.wz, h3]
  · rw [applyF_keep hf (nin w (by simp)) (nout w (by simp)), hw]
  · rw [applyF_keep hf (nin y2 (by simp)) (nout y2 (by simp)), applyF_keep hf (nin y1 (by simp))
      (nout y1 (by simp)), hy2]
  · rw [applyF_noout hf (nout z (by simp)), applyF_noout hfτ (nout z (by simp)), s_push hf (nin x (by simp)),
      s_push hf (nin y (by simp)), s_push hfτ (nin x (by simp)), s_push hfτ (nin y (by simp)),
      applyF_keep hf (nin y1 (by simp)) (nout y1 (by simp)), tx, ty, tz, hD, ← List.append_assoc (σ' y1),
      zw_cont _ (σ' x) (σ' y1 ++ σ' y), ← hE, List.append_assoc, List.append_assoc,
      List.drop_append_of_le_length kk]
    simp
  · rw [s_push hf (nin x (by simp)), s_push hf (nin y (by simp)), s_push hfτ (nin x (by simp)),
      s_push hfτ (nin y (by simp)), applyF_keep hf (nin y1 (by simp)) (nout y1 (by simp)), tx, ty,
      ← List.append_assoc, lft_cont (σ' x) (σ' y1 ++ σ' y), ← hE]

theorem bwd_termS (P : PatS rs rs' p q r x y y1 y2 w z F F1 F2) :
    ∀ t' σ, RelS x y y1 y2 w z F F1 σ t' → Terminal (step (graph rs')) t' →
      ∃ τ n, Run (step (graph rs)) σ n τ ∧ Terminal (step (graph rs)) τ ∧
        ∀ ch, ch ≠ x → ch ≠ y → ch ≠ y1 → ch ≠ y2 → ch ≠ w → τ ch = t' ch := by
  have M := ne6 P.hnd
  intro t' σ ⟨hR, h1, h2, h3, Xw, Yw, hl, hw, hy2, hD, hE⟩ ht
  have ty := term_fork2 P.hp' M.yy1 M.yy2 M.y1y2 ht
  have tq := term_comp2 P.hq' M.xy1 M.xw M.y1w ht
  have tr := term_comp2 P.hr' M.y2w M.y2z M.wz ht
  have hYw : Yw = [] := by
    rcases tr with h | h
    · rw [hy2] at h; exact (List.append_eq_nil_iff.mp h).1
    · rw [hw] at h
      cases Xw with
      | nil => cases Yw with
        | nil => rfl
        | cons _ _ => simp at hl
      | cons a _ => cases Yw with
        | nil => simp at hl
        | cons _ _ => simp at h
  subst hYw
  have hXw : Xw = [] := List.eq_nil_of_length_eq_zero hl
  subst hXw
  rw [ty, List.append_nil, lft_of_empty tq] at hE
  rw [ty, List.append_nil, zw_of_empty _ tq] at hD
  obtain ⟨τ, n, hrun, tx, tyy, tz, tR⟩ := flushSA P σ
  have agree : ∀ ch, ch ≠ x → ch ≠ y → ch ≠ y1 → ch ≠ y2 → ch ≠ w → τ ch = t' ch := by
    intro ch k1 k2 k3 k4 k5
    by_cases k6 : ch = z
    · subst k6; rw [tz, hD]; simp
    · rw [tR ch k1 k2 k6, hR ch k1 k2 k3 k4 k5 k6]
  refine ⟨τ, n, hrun, ?_, agree⟩
  intro l
  by_cases lp : l = p
  · subst lp
    refine step_comp2_none P.hp ?_
    rw [tx, tyy, hE]; exact tq
  have hl0 : l ≠ q ∧ l ≠ r ∨ ¬ (l ≠ q ∧ l ≠ r) := Classical.em _
  rcases hl0 with ⟨lq, lr⟩ | hqr
  · refine other_none (P.hsame l lp lq lr).symm (ht l) ?_
    intro r0 hr0 ch hch
    have hr1 : rs[l]? = some r0 := by rw [← P.hsame l lp lq lr]; exact hr0
    have := s_nin P lp hr1 ch
    exact agree ch (fun h => this (Or.inl h) hch) (fun h => this (Or.inr (Or.inl h)) hch)
      (fun h => this (Or.inr (Or.inr (Or.inl h))) hch) (fun h => this (Or.inr (Or.inr (Or.inr (Or.inl h)))) hch)
      (fun h => this (Or.inr (Or.inr (Or.inr (Or.inr h)))) hch)
  · have : l = q ∨ l = r := by
      by_cases a : l = q
      · exact Or.inl a
      · exact Or.inr (Classical.byContradiction fun b => hqr ⟨a, b⟩)
    rcases this with rfl | rfl
    · exact step_graph_none P.hq τ
    · exact step_graph_none P.hr τ

theorem split_forward (P : PatS rs rs' p q r x y y1 y2 w z F F1 F2) {σ0 t : Store Nat Nat} {n : Nat}
    (h0 : σ0 y1 = [] ∧ σ0 y2 = [] ∧ σ0 w = [])
    (hr : Run (step (graph rs)) σ0 n t) (ht : Terminal (step (graph rs)) t) :
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧
      ∀ ch, ch ≠ x → ch ≠ y → ch ≠ y1 → ch ≠ y2 → ch ≠ w → t' ch = t ch := by
  obtain ⟨a1, a2, a3⟩ := h0
  exact sim_complete (RelS x y y1 y2 w z F F1)
    (fun t t' => ∀ ch, ch ≠ x → ch ≠ y → ch ≠ y1 → ch ≠ y2 → ch ≠ w → t' ch = t ch)
    (fwd_stepS P) (fwd_termS P) hr ht σ0
    ⟨fun _ _ _ _ _ _ _ => rfl, a1, a2, a3, [], [], rfl, by simp [a3], by simp [a2, a1], by simp [a1],
      by simp [a1]⟩

theorem split_backward (P : PatS rs rs' p q r x y y1 y2 w z F F1 F2) {σ0 t' : Store Nat Nat} {n : Nat}
    (h0 : σ0 y1 = [] ∧ σ0 y2 = [] ∧ σ0 w = [])
    (hr : Run (step (graph rs')) σ0 n t') (ht : Terminal (step (graph rs')) t') :
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧
      ∀ ch, ch ≠ x → ch ≠ y → ch ≠ y1 → ch ≠ y2 → ch ≠ w → t ch = t' ch := by
  obtain ⟨a1, a2, a3⟩ := h0
  exact sim_complete (fun σ' σ => RelS x y y1 y2 w z F F1 σ σ')
    (fun t' t => ∀ ch, ch ≠ x → ch ≠ y → ch ≠ y1 → ch ≠ y2 → ch ≠ w → t ch = t' ch)
    (bwd_stepS P) (bwd_termS P) hr ht σ0
    ⟨fun _ _ _ _ _ _ _ => rfl, a1, a2, a3, [], [], rfl, by simp [a3], by simp [a2, a1], by simp [a1],
      by simp [a1]⟩

end Split

end Formal.Rewrite.IncCmp
