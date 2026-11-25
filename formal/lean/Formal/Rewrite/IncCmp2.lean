import Formal.Rewrite.IncCmp2Lib

/-!
# Formal.Rewrite.IncCmp2 — moving a loop test before its increment, compare with a second input channel (shard A, 2026-11-18)

**Problem, plainly.** In the loop tests of research's automatic-path kernels the compare reads a second CHANNEL, not
a literal: the loop bound `n` on a ring (countloop, horner, brhash, xorshift) or a constant fired by a control token
(lfsrfind). The frontend emits `s = addi e, k ; (s0, s1) = fork s ; c = cmpi P, s1, K`, so the test waits for the
increment. The rewrite: `(e0, e1) = fork e ; s0 = addi e0, k ; c = cmpi' e1, K`. Same function, whatever the rest of
the graph does?

**Proved** (`forward2`, `backward2`): for ANY imported graph `rs` holding `comp [e] s fA`, `fork s [s0, s1]`,
`comp [s1, k] c fC` at labels `b d f`, and `rs'` equal except for `fork e [e0, e1]`, `comp [e0] s0 fA`,
`comp [e1, k] c fC'` there, with fresh internal channels (`s s1 e0 e1`), nothing else reading `e`, `k` or the
internal channels or producing `s0`, `c`, and the per-token identity `∀ v w, fC(fA v, w) = fC'(v, w)`: from any store
with empty internal channels, every complete run of either graph is matched by a complete run of the other that ends
in the same store outside `s s1 e0 e1`. Generic over `fA fC fC'`.

**How.** Unlike the one-input case, the compare can stall for want of a `k` token, so the two graphs cannot be
flushed to the same state. The relation compares what each graph has "virtually" produced: `s0` plus the
increments still inside, `c` plus the pairs the compare can still form, and the leftovers of that pairing (`lft`);
internal firings leave all three unchanged.

**Not covered:** token level only; the arithmetic instances of the identity (`IncCmpArith`); that the rewrite
tool's output imports to `rs'` (checked per kernel).
-/

namespace Formal.Rewrite.IncCmp

open Formal.Net.Kahn Formal.Net.GcdHw

section Pattern2

variable {rs rs' : List Rule} {b d f e s s0 s1 c k e0 e1 : Nat} {fA fC fC' : E}

structure Pat2 (rs rs' : List Rule) (b d f e s s0 s1 c k e0 e1 : Nat) (fA fC fC' : E) : Prop where
  hb : rs[b]? = some (.comp [e] s fA)
  hb' : rs'[b]? = some (.fork e [e0, e1])
  hd : rs[d]? = some (.fork s [s0, s1])
  hd' : rs'[d]? = some (.comp [e0] s0 fA)
  hf : rs[f]? = some (.comp [s1, k] c fC)
  hf' : rs'[f]? = some (.comp [e1, k] c fC')
  hsame : ∀ l, l ≠ b → l ≠ d → l ≠ f → rs'[l]? = rs[l]?
  hins : ∀ l r, l ≠ b → l ≠ d → l ≠ f → rs[l]? = some r →
    ∀ ch ∈ r.insL, ch ≠ e ∧ ch ≠ s ∧ ch ≠ s1 ∧ ch ≠ e0 ∧ ch ≠ e1 ∧ ch ≠ k
  houts : ∀ l r, l ≠ b → l ≠ d → l ≠ f → rs[l]? = some r →
    ∀ ch ∈ r.outsL, ch ≠ s ∧ ch ≠ s1 ∧ ch ≠ e0 ∧ ch ≠ e1 ∧ ch ≠ s0 ∧ ch ≠ c
  hnd : [k, e, s, s0, s1, c, e0, e1].Nodup
  hbd : b ≠ d
  hbf : b ≠ f
  hdf : d ≠ f
  hH : ∀ v w, fC.eval [fA.eval [v], w] = fC'.eval [v, w]

/-- What each graph has virtually produced, and what is left to pair. -/
def Rel2 (e s s0 s1 c k e0 e1 : Nat) (fA fC fC' : E) (σ σ' : Store Nat Nat) : Prop :=
  (∀ ch, ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → ch ≠ s0 → ch ≠ c → ch ≠ k → σ' ch = σ ch) ∧
  σ e0 = [] ∧ σ e1 = [] ∧ σ' s = [] ∧ σ' s1 = [] ∧
  σ s0 ++ σ s = σ' s0 ++ (σ' e0).map (fun v => fA.eval [v]) ∧
  σ c ++ List.zipWith (fun a w => fC.eval [a, w]) (σ s1 ++ σ s) (σ k) =
    σ' c ++ List.zipWith (fun a w => fC'.eval [a, w]) (σ' e1) (σ' k) ∧
  (lft (σ s1 ++ σ s) (σ k)).1 = (lft (σ' e1) (σ' k)).1.map (fun v => fA.eval [v]) ∧
  (lft (σ s1 ++ σ s) (σ k)).2 = (lft (σ' e1) (σ' k)).2

theorem lft_of_empty {X K : List Nat} (h : X = [] ∨ K = []) : lft X K = (X, K) := by
  rcases h with rfl | rfl <;> simp

theorem zw_of_empty (g : Nat → Nat → Nat) {X K : List Nat} (h : X = [] ∨ K = []) : List.zipWith g X K = [] := by
  rcases h with rfl | rfl <;> simp

theorem lft_idem (X K : List Nat) : lft (lft X K).1 (lft X K).2 = lft X K := lft_of_empty (lft_one_empty X K)

theorem zw_lft (g : Nat → Nat → Nat) (X K : List Nat) : List.zipWith g (lft X K).1 (lft X K).2 = [] :=
  zw_of_empty g (lft_one_empty X K)

theorem zw_hH (P : Pat2 rs rs' b d f e s s0 s1 c k e0 e1 fA fC fC') (X K : List Nat) :
    List.zipWith (fun a w => fC.eval [a, w]) (X.map (fun v => fA.eval [v])) K =
      List.zipWith (fun a w => fC'.eval [a, w]) X K := by
  rw [zw_map]; congr 1; funext a w; exact P.hH a w

/-- The rewritten graph's flush: drain `e0`, then pair `e1` with `k` as far as possible. -/
theorem flushB2 (P : Pat2 rs rs' b d f e s s0 s1 c k e0 e1 fA fC fC') (σ : Store Nat Nat) :
    ∃ τ n, Run (step (graph rs')) σ n τ ∧ τ e0 = [] ∧
      τ s0 = σ s0 ++ (σ e0).map (fun v => fA.eval [v]) ∧
      τ e1 = (lft (σ e1) (σ k)).1 ∧ τ k = (lft (σ e1) (σ k)).2 ∧
      τ c = σ c ++ List.zipWith (fun a w => fC'.eval [a, w]) (σ e1) (σ k) ∧
      ∀ ch, ch ≠ e0 → ch ≠ s0 → ch ≠ e1 → ch ≠ k → ch ≠ c → τ ch = σ ch := by
  have N := ne8 P.hnd
  obtain ⟨n1, r1⟩ := drain_comp1 P.hd' (Ne.symm N.s0e0) (σ e0) σ rfl
  let σ1 := upd (upd σ e0 []) s0 (σ s0 ++ (σ e0).map (fun v => fA.eval [v]))
  obtain ⟨n2, r2⟩ := drain_comp2 P.hf' (Ne.symm N.xe1) (Ne.symm N.ce1) N.xc (σ1 e1) (σ1 k) σ1 rfl rfl
  refine ⟨_, _, run_trans r1 r2, ?_⟩
  simp only [σ1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · nsimp
  · nsimp
  · nsimp
  · nsimp
  · nsimp
  · intro ch h1 h2 h3 h4 h5; simp [upd, h1, h2, h3, h4, h5]

/-- The original graph's flush: drain `s` through the fork, then pair `s1` with `k` as far as possible. -/
theorem flushA2 (P : Pat2 rs rs' b d f e s s0 s1 c k e0 e1 fA fC fC') (σ : Store Nat Nat) :
    ∃ τ n, Run (step (graph rs)) σ n τ ∧ τ s = [] ∧ τ s0 = σ s0 ++ σ s ∧
      τ s1 = (lft (σ s1 ++ σ s) (σ k)).1 ∧ τ k = (lft (σ s1 ++ σ s) (σ k)).2 ∧
      τ c = σ c ++ List.zipWith (fun a w => fC.eval [a, w]) (σ s1 ++ σ s) (σ k) ∧
      ∀ ch, ch ≠ s → ch ≠ s0 → ch ≠ s1 → ch ≠ k → ch ≠ c → τ ch = σ ch := by
  have N := ne8 P.hnd
  obtain ⟨n1, r1⟩ := drain_fork2 P.hd N.ss0 N.ss1 N.s0s1 (σ s) σ rfl
  let σ1 := upd (upd (upd σ s []) s0 (σ s0 ++ σ s)) s1 (σ s1 ++ σ s)
  obtain ⟨n2, r2⟩ := drain_comp2 P.hf (Ne.symm N.xs1) N.s1c N.xc (σ1 s1) (σ1 k) σ1 rfl rfl
  refine ⟨_, _, run_trans r1 r2, ?_⟩
  simp only [σ1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · nsimp
  · nsimp
  · nsimp
  · nsimp
  · nsimp
  · intro ch h1 h2 h3 h4 h5; simp [upd, h1, h2, h3, h4, h5]

set_option hygiene false in
/-- Evaluate nested `upd`s at a channel without touching the rest of the goal. -/
macro "nso" : tactic => `(tactic| simp only [upd, N.xe, N.xs, N.xs0, N.xs1, N.xc, N.xe0, N.xe1, N.es, N.es0, N.es1,
  N.ec, N.ee0, N.ee1, N.ss0, N.ss1, N.sc, N.se0, N.se1, N.s0s1, N.s0c, N.s0e0, N.s0e1, N.s1c, N.s1e0, N.s1e1,
  N.ce0, N.ce1, N.e0e1, N.xe.symm, N.xs.symm, N.xs0.symm, N.xs1.symm, N.xc.symm, N.xe0.symm, N.xe1.symm,
  N.es.symm, N.es0.symm, N.es1.symm, N.ec.symm, N.ee0.symm, N.ee1.symm, N.ss0.symm, N.ss1.symm, N.sc.symm,
  N.se0.symm, N.se1.symm, N.s0s1.symm, N.s0c.symm, N.s0e0.symm, N.s0e1.symm, N.s1c.symm, N.s1e0.symm,
  N.s1e1.symm, N.ce0.symm, N.ce1.symm, N.e0e1.symm, ↓reduceIte, if_true, if_false])

theorem zw_one (P : Pat2 rs rs' b d f e s s0 s1 c k e0 e1 fA fC fC') (v : Nat) (L : List Nat) :
    List.zipWith (fun a w => fC.eval [a, w]) [fA.eval [v]] L = List.zipWith (fun a w => fC'.eval [a, w]) [v] L := by
  cases L with
  | nil => rfl
  | cons w ws => simp [P.hH]

/-- Appending one increment on each side keeps the pairing relation. -/
theorem rel_app1 (P : Pat2 rs rs' b d f e s s0 s1 c k e0 e1 fA fC fC') {X K X' K' : List Nat} (v : Nat)
    (hL1 : (lft X K).1 = (lft X' K').1.map (fun v => fA.eval [v])) (hL2 : (lft X K).2 = (lft X' K').2) :
    (lft (X ++ [fA.eval [v]]) K).1 = (lft (X' ++ [v]) K').1.map (fun v => fA.eval [v]) ∧
    (lft (X ++ [fA.eval [v]]) K).2 = (lft (X' ++ [v]) K').2 := by
  rw [lft_app_left, lft_app_left]
  by_cases hx : (lft X' K').1 = []
  · have hx2 : (lft X K).1 = [] := by rw [hL1, hx]; rfl
    rw [if_pos hx, if_pos hx2, hL2]
    have := lft_map (fun v => fA.eval [v]) [v] (lft X' K').2
    simp only [List.map_cons, List.map_nil] at this
    rw [this]; exact ⟨rfl, rfl⟩
  · have hx2 : (lft X K).1 ≠ [] := by rw [hL1]; intro h; exact hx (List.map_eq_nil_iff.mp h)
    rw [if_neg hx, if_neg hx2, hL1, hL2]; simp

/-- Appending `ys` to `k` on both sides keeps the pairing relation. -/
theorem rel_appk (P : Pat2 rs rs' b d f e s s0 s1 c k e0 e1 fA fC fC') {X K X' K' : List Nat} (ys : List Nat)
    (hL1 : (lft X K).1 = (lft X' K').1.map (fun v => fA.eval [v])) (hL2 : (lft X K).2 = (lft X' K').2) :
    (lft X (K ++ ys)).1 = (lft X' (K' ++ ys)).1.map (fun v => fA.eval [v]) ∧
    (lft X (K ++ ys)).2 = (lft X' (K' ++ ys)).2 := by
  rw [lft_app_right, lft_app_right]
  by_cases hk : (lft X' K').2 = []
  · have hk2 : (lft X K).2 = [] := by rw [hL2, hk]
    rw [if_pos hk, if_pos hk2, hL1, lft_map]; exact ⟨rfl, rfl⟩
  · have hk2 : (lft X K).2 ≠ [] := by rw [hL2]; exact hk
    rw [if_neg hk, if_neg hk2, hL1, hL2]; exact ⟨rfl, rfl⟩

theorem fwd_step2 (P : Pat2 rs rs' b d f e s s0 s1 c k e0 e1 fA fC fC') :
    ∀ σ σ' l σ1, Rel2 e s s0 s1 c k e0 e1 fA fC fC' σ σ' → step (graph rs) σ l = some σ1 →
      ∃ σ1' n, Run (step (graph rs')) σ' n σ1' ∧ Rel2 e s s0 s1 c k e0 e1 fA fC fC' σ1 σ1' := by
  have N := ne8 P.hnd
  intro σ σ' l σ1 ⟨hR, h0, h1, h2, h3, hS0, hC, hL1, hL2⟩ hst
  by_cases lb : l = b
  · subst lb
    cases he : σ e with
    | nil => rw [step_comp1_none P.hb he] at hst; cases hst
    | cons v vs =>
      rw [step_comp1 P.hb N.es he] at hst; cases hst
      have he' : σ' e = v :: vs := by rw [hR e N.es N.es1 N.ee0 N.ee1 N.es0 N.ec N.xe.symm, he]
      have L := rel_app1 P v hL1 hL2
      refine ⟨_, 1, run_one (step_fork2 P.hb' N.ee0 N.ee1 N.e0e1 he'), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro ch k1 k2 k3 k4 k5 k6 k7
        by_cases ke : ch = e
        · subst ke; simp [upd, N.ee0, N.ee1, N.es]
        · simp [upd, ke, k1, k3, k4, hR ch k1 k2 k3 k4 k5 k6 k7]
      · nso; exact h0
      · nso; exact h1
      · nso; exact h2
      · nso; exact h3
      · nso; rw [List.map_append, ← List.append_assoc, ← List.append_assoc, ← hS0]; simp
      · nso
        rw [← List.append_assoc, zw_app_left _ (σ s1 ++ σ s) [fA.eval [v]] (σ k),
          zw_app_left _ (σ' e1) [v] (σ' k), ← List.append_assoc, ← List.append_assoc, hC, hL2, zw_one P]
      · nso; rw [← List.append_assoc]; exact L.1
      · nso; rw [← List.append_assoc]; exact L.2
  by_cases ld : l = d
  · subst ld
    cases hs : σ s with
    | nil => rw [step_fork2_none P.hd hs] at hst; cases hst
    | cons u us =>
      rw [step_fork2 P.hd N.ss0 N.ss1 N.s0s1 hs] at hst; cases hst
      have hX : σ s1 ++ [u] ++ us = σ s1 ++ σ s := by rw [hs]; simp
      refine ⟨σ', 0, Run.refl _, ?_, ?_, ?_, h2, h3, ?_, ?_, ?_, ?_⟩
      · intro ch k1 k2 k3 k4 k5 k6 k7; simp [upd, k1, k2, k5, hR ch k1 k2 k3 k4 k5 k6 k7]
      · nso; exact h0
      · nso; exact h1
      · nso; rw [← hS0, hs]; simp
      · nso; rw [hX]; exact hC
      · nso; rw [hX]; exact hL1
      · nso; rw [hX]; exact hL2
  by_cases lf : l = f
  · subst lf
    cases hs1 : σ s1 with
    | nil => rw [step_comp2_none P.hf (Or.inl hs1)] at hst; cases hst
    | cons a as =>
      cases hk : σ k with
      | nil => rw [step_comp2_none P.hf (Or.inr hk)] at hst; cases hst
      | cons w ws =>
        rw [step_comp2 P.hf (Ne.symm N.xs1) N.s1c N.xc hs1 hk] at hst; cases hst
        refine ⟨σ', 0, Run.refl _, ?_, ?_, ?_, h2, h3, ?_, ?_, ?_, ?_⟩
        · intro ch k1 k2 k3 k4 k5 k6 k7; simp [upd, k2, k6, k7, hR ch k1 k2 k3 k4 k5 k6 k7]
        · nso; exact h0
        · nso; exact h1
        · nso; exact hS0
        · nso; rw [← hC, hs1, hk]; simp
        · nso; rw [← hL1, hs1, hk]; rfl
        · nso; rw [← hL2, hs1, hk]; rfl
  -- an outside rule: flush the rewritten graph, then fire it there
  obtain ⟨r, fr, hr, hf, rfl⟩ := step_some_rule hst
  have hin := P.hins l r lb ld lf hr
  have hout := P.houts l r lb ld lf hr
  obtain ⟨τ, n, hrun, t0, tS0, tE1, tK, tC, tR⟩ := flushB2 P σ'
  have hfτ : r.fire natVI τ = some fr := by
    refine fire_mono hf ?_
    intro ch hch
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hin ch hch
    by_cases k7 : ch = s0
    · subst k7; exact ⟨_, by rw [tS0, ← hS0]⟩
    · by_cases k8 : ch = c
      · subst k8; exact ⟨_, by rw [tC, ← hC]⟩
      · exact ⟨[], by rw [List.append_nil, tR ch k4 k7 k5 k6 k8, hR ch k2 k3 k4 k5 k7 k8 k6]⟩
  have hst' : step (graph rs') τ l = some (applyF τ fr) := by
    rw [step_graph (by rw [P.hsame l lb ld lf]; exact hr), hfτ]; rfl
  have nin : ∀ ch, (ch = e ∨ ch = s ∨ ch = s1 ∨ ch = e0 ∨ ch = e1 ∨ ch = k) → ch ∉ r.insL := by
    intro ch hc hm; obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hin ch hm
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  have nout : ∀ ch, (ch = s ∨ ch = s1 ∨ ch = e0 ∨ ch = e1 ∨ ch = s0 ∨ ch = c) → ch ∉ r.outsL := by
    intro ch hc hm; obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hout ch hm
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  have kpop : ∀ {ρ : Store Nat Nat}, r.fire natVI ρ = some fr → applyF ρ fr k = ρ k ++ fr.2 k := by
    intro ρ hρ
    have := (r.node natVI).pop_ins ρ fr k hρ (nin k (by simp))
    simp [applyF, this]
  have ks : applyF σ fr s = σ s := applyF_keep hf (nin s (by simp)) (nout s (by simp))
  have ks1 : applyF σ fr s1 = σ s1 := applyF_keep hf (nin s1 (by simp)) (nout s1 (by simp))
  have hkτ := kpop hfτ
  have hkσ := kpop hf
  rw [tK] at hkτ
  have hτ1 : applyF τ fr e1 = (lft (σ' e1) (σ' k)).1 := by
    rw [applyF_keep hfτ (nin e1 (by simp)) (nout e1 (by simp)), tE1]
  have hidem := lft_idem (σ' e1) (σ' k)
  refine ⟨_, n + 1, run_trans hrun (run_one hst'), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ch k1 k2 k3 k4 k5 k6 k7
    simp only [applyF]; rw [tR ch k3 k5 k4 k7 k6, hR ch k1 k2 k3 k4 k5 k6 k7]
  · rw [applyF_keep hf (nin e0 (by simp)) (nout e0 (by simp)), h0]
  · rw [applyF_keep hf (nin e1 (by simp)) (nout e1 (by simp)), h1]
  · rw [applyF_keep hfτ (nin s (by simp)) (nout s (by simp)), tR s N.se0 N.ss0 N.se1 N.xs.symm N.sc, h2]
  · rw [applyF_keep hfτ (nin s1 (by simp)) (nout s1 (by simp)),
      tR s1 N.s1e0 N.s0s1.symm N.s1e1 N.xs1.symm N.s1c, h3]
  · rw [applyF_noout hf (nout s0 (by simp)), applyF_noout hfτ (nout s0 (by simp)), ks,
      applyF_keep hfτ (nin e0 (by simp)) (nout e0 (by simp)), t0, tS0, ← hS0]
    have kk := fire_le hf s0
    simp [List.drop_append_of_le_length kk]
  · rw [applyF_noout hf (nout c (by simp)), applyF_noout hfτ (nout c (by simp)), ks, ks1, hkσ, hkτ, hτ1, tC,
      ← hC, zw_app_right, zw_app_right, ← hidem, zw_lft, hidem, List.nil_append, hL1, zw_hH P]
    have kk := fire_le hf c
    rw [List.drop_append_of_le_length kk, List.append_assoc, hidem]
  · rw [ks, ks1, hkσ, hkτ, hτ1, ← hidem]; rw [hidem]
    have := rel_appk P (fr.2 k) hL1 hL2
    rw [this.1]; congr 2; rw [lft_app_right, lft_app_right, hidem]
  · rw [ks, ks1, hkσ, hkτ, hτ1]
    have := rel_appk P (fr.2 k) hL1 hL2
    rw [this.2, lft_app_right, lft_app_right, hidem]

theorem term_comp2 {rs : List Rule} {l i j o : Nat} {g : E} (hr : rs[l]? = some (.comp [i, j] o g))
    (hij : i ≠ j) (hio : i ≠ o) (hjo : j ≠ o) {σ : Store Nat Nat} (ht : Terminal (step (graph rs)) σ) :
    σ i = [] ∨ σ j = [] := by
  cases hi : σ i with
  | nil => exact Or.inl rfl
  | cons a as =>
    cases hj : σ j with
    | nil => exact Or.inr rfl
    | cons w ws => have := step_comp2 hr hij hio hjo hi hj; rw [ht l] at this; cases this

theorem fwd_term2 (P : Pat2 rs rs' b d f e s s0 s1 c k e0 e1 fA fC fC') :
    ∀ t σ', Rel2 e s s0 s1 c k e0 e1 fA fC fC' t σ' → Terminal (step (graph rs)) t →
      ∃ τ n, Run (step (graph rs')) σ' n τ ∧ Terminal (step (graph rs')) τ ∧
        ∀ ch, ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → τ ch = t ch := by
  have N := ne8 P.hnd
  intro t σ' ⟨hR, h0, h1, h2, h3, hS0, hC, hL1, hL2⟩ ht
  have te := term_comp1 P.hb N.es ht
  have ts := term_fork2 P.hd N.ss0 N.ss1 N.s0s1 ht
  have tf := term_comp2 P.hf (Ne.symm N.xs1) N.s1c N.xc ht
  obtain ⟨τ, n, hrun, t0, tS0, tE1, tK, tC, tR⟩ := flushB2 P σ'
  rw [ts, List.append_nil, lft_of_empty tf] at hL1 hL2
  rw [ts, List.append_nil, zw_of_empty _ tf, List.append_nil] at hC
  rw [ts, List.append_nil] at hS0
  have agree : ∀ ch, ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → τ ch = t ch := by
    intro ch k1 k2 k3 k4
    by_cases k5 : ch = s0
    · subst k5; rw [tS0, ← hS0]
    · by_cases k6 : ch = c
      · subst k6; rw [tC, ← hC]
      · by_cases k7 : ch = k
        · subst k7; rw [tK, ← hL2]
        · rw [tR ch k3 k5 k4 k7 k6, hR ch k1 k2 k3 k4 k5 k6 k7]
  refine ⟨τ, n, hrun, ?_, agree⟩
  intro l
  by_cases lb : l = b
  · subst lb; exact step_fork2_none P.hb' (by rw [agree e N.es N.es1 N.ee0 N.ee1, te])
  by_cases ld : l = d
  · subst ld; exact step_comp1_none P.hd' t0
  by_cases lf : l = f
  · subst lf
    refine step_comp2_none P.hf' ?_
    rcases tf with h | h
    · left; rw [tE1]; rw [h] at hL1; exact (List.map_eq_nil_iff.mp hL1.symm)
    · right; rw [tK, ← hL2, h]
  refine other_none (P.hsame l lb ld lf) (ht l) ?_
  intro r hr ch hch
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := P.hins l r lb ld lf hr ch hch
  exact agree ch k2 k3 k4 k5

theorem bwd_step2 (P : Pat2 rs rs' b d f e s s0 s1 c k e0 e1 fA fC fC') :
    ∀ σ' σ l σ1', Rel2 e s s0 s1 c k e0 e1 fA fC fC' σ σ' → step (graph rs') σ' l = some σ1' →
      ∃ σ1 n, Run (step (graph rs)) σ n σ1 ∧ Rel2 e s s0 s1 c k e0 e1 fA fC fC' σ1 σ1' := by
  have N := ne8 P.hnd
  intro σ' σ l σ1' ⟨hR, h0, h1, h2, h3, hS0, hC, hL1, hL2⟩ hst
  by_cases lb : l = b
  · subst lb
    cases he' : σ' e with
    | nil => rw [step_fork2_none P.hb' he'] at hst; cases hst
    | cons v vs =>
      rw [step_fork2 P.hb' N.ee0 N.ee1 N.e0e1 he'] at hst; cases hst
      have he : σ e = v :: vs := by rw [← hR e N.es N.es1 N.ee0 N.ee1 N.es0 N.ec N.xe.symm, he']
      have L := rel_app1 P v hL1 hL2
      refine ⟨_, 1, run_one (step_comp1 P.hb N.es he), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro ch k1 k2 k3 k4 k5 k6 k7
        by_cases ke : ch = e
        · subst ke; simp [upd, N.ee0, N.ee1, N.es]
        · simp [upd, ke, k1, k3, k4, hR ch k1 k2 k3 k4 k5 k6 k7]
      · nso; exact h0
      · nso; exact h1
      · nso; exact h2
      · nso; exact h3
      · nso; rw [List.map_append, ← List.append_assoc, ← List.append_assoc, ← hS0]; simp
      · nso
        rw [← List.append_assoc, zw_app_left _ (σ s1 ++ σ s) [fA.eval [v]] (σ k),
          zw_app_left _ (σ' e1) [v] (σ' k), ← List.append_assoc, ← List.append_assoc, hC, hL2, zw_one P]
      · nso; rw [← List.append_assoc]; exact L.1
      · nso; rw [← List.append_assoc]; exact L.2
  by_cases ld : l = d
  · subst ld
    cases he0 : σ' e0 with
    | nil => rw [step_comp1_none P.hd' he0] at hst; cases hst
    | cons u us =>
      rw [step_comp1 P.hd' (Ne.symm N.s0e0) he0] at hst; cases hst
      refine ⟨σ, 0, Run.refl _, ?_, h0, h1, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro ch k1 k2 k3 k4 k5 k6 k7; simp [upd, k3, k5, hR ch k1 k2 k3 k4 k5 k6 k7]
      · nso; exact h2
      · nso; exact h3
      · nso; rw [hS0, he0]; simp
      · nso; exact hC
      · nso; exact hL1
      · nso; exact hL2
  by_cases lf : l = f
  · subst lf
    cases he1 : σ' e1 with
    | nil => rw [step_comp2_none P.hf' (Or.inl he1)] at hst; cases hst
    | cons a as =>
      cases hk : σ' k with
      | nil => rw [step_comp2_none P.hf' (Or.inr hk)] at hst; cases hst
      | cons w ws =>
        rw [step_comp2 P.hf' (Ne.symm N.xe1) (Ne.symm N.ce1) N.xc he1 hk] at hst; cases hst
        refine ⟨σ, 0, Run.refl _, ?_, h0, h1, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro ch k1 k2 k3 k4 k5 k6 k7; simp [upd, k4, k6, k7, hR ch k1 k2 k3 k4 k5 k6 k7]
        · nso; exact h2
        · nso; exact h3
        · nso; exact hS0
        · nso; rw [hC, he1, hk]; simp
        · nso; rw [hL1, he1, hk]; rfl
        · nso; rw [hL2, he1, hk]; rfl
  -- an outside rule: flush the original graph, then fire it there
  obtain ⟨r, fr, hr', hf, rfl⟩ := step_some_rule hst
  have hr : rs[l]? = some r := by rw [← P.hsame l lb ld lf]; exact hr'
  have hin := P.hins l r lb ld lf hr
  have hout := P.houts l r lb ld lf hr
  obtain ⟨τ, n, hrun, tS, tS0, tS1, tK, tC, tR⟩ := flushA2 P σ
  have hfτ : r.fire natVI τ = some fr := by
    refine fire_mono hf ?_
    intro ch hch
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hin ch hch
    by_cases k7 : ch = s0
    · subst k7; exact ⟨_, by rw [tS0, hS0]⟩
    · by_cases k8 : ch = c
      · subst k8; exact ⟨_, by rw [tC, hC]⟩
      · exact ⟨[], by rw [List.append_nil, tR ch k2 k7 k3 k6 k8, hR ch k2 k3 k4 k5 k7 k8 k6]⟩
  have hst' : step (graph rs) τ l = some (applyF τ fr) := by
    rw [step_graph hr, hfτ]; rfl
  have nin : ∀ ch, (ch = e ∨ ch = s ∨ ch = s1 ∨ ch = e0 ∨ ch = e1 ∨ ch = k) → ch ∉ r.insL := by
    intro ch hc hm; obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hin ch hm
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  have nout : ∀ ch, (ch = s ∨ ch = s1 ∨ ch = e0 ∨ ch = e1 ∨ ch = s0 ∨ ch = c) → ch ∉ r.outsL := by
    intro ch hc hm; obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hout ch hm
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  have kpop : ∀ {ρ : Store Nat Nat}, r.fire natVI ρ = some fr → applyF ρ fr k = ρ k ++ fr.2 k := by
    intro ρ hρ
    have := (r.node natVI).pop_ins ρ fr k hρ (nin k (by simp))
    simp [applyF, this]
  have ke1 : applyF σ' fr e1 = σ' e1 := applyF_keep hf (nin e1 (by simp)) (nout e1 (by simp))
  have ke0 : applyF σ' fr e0 = σ' e0 := applyF_keep hf (nin e0 (by simp)) (nout e0 (by simp))
  have hkτ := kpop hfτ
  have hkσ := kpop hf
  rw [tK] at hkτ
  have hτs : applyF τ fr s = [] := by rw [applyF_keep hfτ (nin s (by simp)) (nout s (by simp)), tS]
  have hτ1 : applyF τ fr s1 = (lft (σ s1 ++ σ s) (σ k)).1 := by
    rw [applyF_keep hfτ (nin s1 (by simp)) (nout s1 (by simp)), tS1]
  have hidem := lft_idem (σ s1 ++ σ s) (σ k)
  refine ⟨_, n + 1, run_trans hrun (run_one hst'), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ch k1 k2 k3 k4 k5 k6 k7
    simp only [applyF]; rw [tR ch k1 k5 k2 k7 k6, hR ch k1 k2 k3 k4 k5 k6 k7]
  · rw [applyF_keep hfτ (nin e0 (by simp)) (nout e0 (by simp)),
      tR e0 N.se0.symm N.s0e0.symm N.s1e0.symm N.xe0.symm N.ce0.symm, h0]
  · rw [applyF_keep hfτ (nin e1 (by simp)) (nout e1 (by simp)),
      tR e1 N.se1.symm N.s0e1.symm N.s1e1.symm N.xe1.symm N.ce1.symm, h1]
  · rw [applyF_keep hf (nin s (by simp)) (nout s (by simp)), h2]
  · rw [applyF_keep hf (nin s1 (by simp)) (nout s1 (by simp)), h3]
  · rw [applyF_noout hfτ (nout s0 (by simp)), applyF_noout hf (nout s0 (by simp)), hτs, ke0, tS0, hS0]
    have kk := fire_le hf s0
    simp [List.drop_append_of_le_length kk]
  · have A : List.zipWith (fun a w => fC.eval [a, w]) (lft (σ s1 ++ σ s) (σ k)).1
        ((lft (σ s1 ++ σ s) (σ k)).2 ++ fr.2 k) =
        List.zipWith (fun a w => fC'.eval [a, w]) (lft (σ' e1) (σ' k)).1 (fr.2 k) := by
      rw [zw_app_right, hidem, zw_lft, List.nil_append, hL1, zw_hH P]
    have kk := fire_le hf c
    rw [applyF_noout hfτ (nout c (by simp)), applyF_noout hf (nout c (by simp)), hτs, hτ1, hkτ, hkσ, ke1, tC,
      hC, List.append_nil, A, zw_app_right, List.drop_append_of_le_length kk, List.append_assoc]
  · rw [hτs, hτ1, hkτ, hkσ, ke1, List.append_nil]
    have := rel_appk P (fr.2 k) hL1 hL2
    rw [lft_app_right (lft (σ s1 ++ σ s) (σ k)).1, hidem, ← this.1, lft_app_right]
  · rw [hτs, hτ1, hkτ, hkσ, ke1, List.append_nil]
    have := rel_appk P (fr.2 k) hL1 hL2
    rw [lft_app_right (lft (σ s1 ++ σ s) (σ k)).1, hidem, ← this.2, lft_app_right]

theorem bwd_term2 (P : Pat2 rs rs' b d f e s s0 s1 c k e0 e1 fA fC fC') :
    ∀ t' σ, Rel2 e s s0 s1 c k e0 e1 fA fC fC' σ t' → Terminal (step (graph rs')) t' →
      ∃ τ n, Run (step (graph rs)) σ n τ ∧ Terminal (step (graph rs)) τ ∧
        ∀ ch, ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → τ ch = t' ch := by
  have N := ne8 P.hnd
  intro t' σ ⟨hR, h0, h1, h2, h3, hS0, hC, hL1, hL2⟩ ht
  have te := term_fork2 P.hb' N.ee0 N.ee1 N.e0e1 ht
  have te0 := term_comp1 P.hd' (Ne.symm N.s0e0) ht
  have tf := term_comp2 P.hf' (Ne.symm N.xe1) (Ne.symm N.ce1) N.xc ht
  obtain ⟨τ, n, hrun, tS, tS0, tS1, tK, tC, tR⟩ := flushA2 P σ
  rw [lft_of_empty tf] at hL1 hL2
  rw [zw_of_empty _ tf, List.append_nil] at hC
  rw [te0, List.map_nil, List.append_nil] at hS0
  have agree : ∀ ch, ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → τ ch = t' ch := by
    intro ch k1 k2 k3 k4
    by_cases k5 : ch = s0
    · subst k5; rw [tS0, hS0]
    · by_cases k6 : ch = c
      · subst k6; rw [tC, hC]
      · by_cases k7 : ch = k
        · subst k7; rw [tK, hL2]
        · rw [tR ch k1 k5 k2 k7 k6, hR ch k1 k2 k3 k4 k5 k6 k7]
  refine ⟨τ, n, hrun, ?_, agree⟩
  intro l
  by_cases lb : l = b
  · subst lb; exact step_comp1_none P.hb (by rw [agree e N.es N.es1 N.ee0 N.ee1, te])
  by_cases ld : l = d
  · subst ld; exact step_fork2_none P.hd tS
  by_cases lf : l = f
  · subst lf
    refine step_comp2_none P.hf ?_
    rcases tf with h | h
    · left; rw [tS1, hL1, h]; rfl
    · right; rw [tK, hL2, h]
  refine other_none (P.hsame l lb ld lf).symm (ht l) ?_
  intro r hr ch hch
  have hr0 : rs[l]? = some r := by rw [← P.hsame l lb ld lf]; exact hr
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := P.hins l r lb ld lf hr0 ch hch
  exact agree ch k2 k3 k4 k5

/-! ## The theorems -/

theorem forward2 (P : Pat2 rs rs' b d f e s s0 s1 c k e0 e1 fA fC fC') {σ0 t : Store Nat Nat} {n : Nat}
    (h0 : σ0 s = [] ∧ σ0 s1 = [] ∧ σ0 e0 = [] ∧ σ0 e1 = [])
    (hr : Run (step (graph rs)) σ0 n t) (ht : Terminal (step (graph rs)) t) :
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧
      ∀ ch, ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → t' ch = t ch := by
  obtain ⟨hs, hs1, he0, he1⟩ := h0
  exact sim_complete (Rel2 e s s0 s1 c k e0 e1 fA fC fC')
    (fun t t' => ∀ ch, ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → t' ch = t ch)
    (fwd_step2 P) (fwd_term2 P) hr ht σ0
    ⟨fun _ _ _ _ _ _ _ _ => rfl, he0, he1, hs, hs1, by simp [hs, he0], by simp [hs, hs1, he1],
      by simp [hs, hs1, he1], by simp [hs, hs1, he1]⟩

theorem backward2 (P : Pat2 rs rs' b d f e s s0 s1 c k e0 e1 fA fC fC') {σ0 t' : Store Nat Nat} {n : Nat}
    (h0 : σ0 s = [] ∧ σ0 s1 = [] ∧ σ0 e0 = [] ∧ σ0 e1 = [])
    (hr : Run (step (graph rs')) σ0 n t') (ht : Terminal (step (graph rs')) t') :
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧
      ∀ ch, ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → t ch = t' ch := by
  obtain ⟨hs, hs1, he0, he1⟩ := h0
  exact sim_complete (fun σ' σ => Rel2 e s s0 s1 c k e0 e1 fA fC fC' σ σ')
    (fun t' t => ∀ ch, ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → t ch = t' ch)
    (bwd_step2 P) (bwd_term2 P) hr ht σ0
    ⟨fun _ _ _ _ _ _ _ _ => rfl, he0, he1, hs, hs1, by simp [hs, he0], by simp [hs, hs1, he1],
      by simp [hs, hs1, he1], by simp [hs, hs1, he1]⟩

end Pattern2

end Formal.Rewrite.IncCmp
