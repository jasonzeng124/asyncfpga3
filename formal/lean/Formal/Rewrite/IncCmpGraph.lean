import Formal.Rewrite.IncCmpLib

/-!
# Formal.Rewrite.IncCmpGraph — moving a loop test before its increment preserves every complete run (shard A, 2026-11-18)

**Problem, plainly.** In 121 of the 166 loop tests of research's suite fixtures the frontend emits
`e = extui x ; s = addi e, k ; (s0, s1) = fork s ; c = cmpi P, s1, C` — the loop test reads the counter AFTER
its increment, so the compare waits for the add. The rewrite makes the test read the counter before the
increment: `e = extui x ; (e0, e1) = fork e ; s0 = addi e0, k ; c = cmpi P, e1, C'`. Is the rewritten graph's
behaviour the same as the original's, whatever the rest of the graph is?

**Proved** (`forward`, `backward`), for ANY imported graph `rs` (any other rules, any channels) that contains the
four rules at labels `a b d f`, and `rs'` equal to `rs` except that those labels carry the rewritten rules, with
fresh internal channels and the per-token identity `hH : ∀ v, fC(fA(fX v)) = fC'(fX v)`:
from any store whose internal channels (`e s s1 e0 e1`) are empty, every complete run of `rs` is matched by a
complete run of `rs'` that ends in the same store on every channel except those five, and vice versa. So both
graphs terminate on the same inputs, with the same outputs (and, with `GcdHw.determinate`, every complete run of
either ends there). The expressions `fX fA fC fC'` are arbitrary; `IncCmpArith` proves `hH` for the instances the
rewrite tool emits (`fX = extui`, `fA = addi k`, `fC = cmpi P _ C`).

**Not covered:** token level only (no gates, delays or cells); that the rewrite tool's MLIR output imports to
exactly `rs'` (checked per kernel, not here); pattern shapes other than this one (45 of the 166 tests).
-/

namespace Formal.Rewrite.IncCmp

open Formal.Net.Kahn Formal.Net.GcdHw

section Pattern

variable {rs rs' : List Rule} {a b d f x e s s0 s1 c e0 e1 : Nat} {fX fA fC fC' : E}

/-- The hypotheses: where the four rules are, that nothing else touches the internal channels or produces the
two outputs, distinct channels, and the per-token identity. -/
structure Pat (rs rs' : List Rule) (a b d f x e s s0 s1 c e0 e1 : Nat) (fX fA fC fC' : E) : Prop where
  ha : rs[a]? = some (.comp [x] e fX)
  ha' : rs'[a]? = some (.comp [x] e fX)
  hb : rs[b]? = some (.comp [e] s fA)
  hb' : rs'[b]? = some (.fork e [e0, e1])
  hd : rs[d]? = some (.fork s [s0, s1])
  hd' : rs'[d]? = some (.comp [e0] s0 fA)
  hf : rs[f]? = some (.comp [s1] c fC)
  hf' : rs'[f]? = some (.comp [e1] c fC')
  hsame : ∀ l, l ≠ a → l ≠ b → l ≠ d → l ≠ f → rs'[l]? = rs[l]?
  hins : ∀ l r, l ≠ a → l ≠ b → l ≠ d → l ≠ f → rs[l]? = some r →
    ∀ ch ∈ r.insL, ch ≠ e ∧ ch ≠ s ∧ ch ≠ s1 ∧ ch ≠ e0 ∧ ch ≠ e1
  houts : ∀ l r, l ≠ a → l ≠ b → l ≠ d → l ≠ f → rs[l]? = some r →
    ∀ ch ∈ r.outsL, ch ≠ e ∧ ch ≠ s ∧ ch ≠ s1 ∧ ch ≠ e0 ∧ ch ≠ e1 ∧ ch ≠ s0 ∧ ch ≠ c
  hnd : [x, e, s, s0, s1, c, e0, e1].Nodup
  hab : a ≠ b
  had : a ≠ d
  haf : a ≠ f
  hbd : b ≠ d
  hbf : b ≠ f
  hdf : d ≠ f
  hH : ∀ v, fC.eval [fA.eval [fX.eval [v]]] = fC'.eval [fX.eval [v]]

/-- The relation: equal outside the pattern, and each output's tokens plus what the pattern still holds for it
agree. -/
def Rel (x e s s0 s1 c e0 e1 : Nat) (fA fC fC' : E) (σ σ' : Store Nat Nat) : Prop :=
  (∀ ch, ch ≠ e → ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → ch ≠ s0 → ch ≠ c → σ' ch = σ ch) ∧
  σ e0 = [] ∧ σ e1 = [] ∧ σ' s = [] ∧ σ' s1 = [] ∧
  σ s0 ++ σ s ++ (σ e).map (fun v => fA.eval [v]) =
    σ' s0 ++ (σ' e0).map (fun v => fA.eval [v]) ++ (σ' e).map (fun v => fA.eval [v]) ∧
  σ c ++ (σ s1).map (fun v => fC.eval [v]) ++ (σ s).map (fun v => fC.eval [v]) ++
      (σ e).map (fun v => fC.eval [fA.eval [v]]) =
    σ' c ++ (σ' e1).map (fun v => fC'.eval [v]) ++ (σ' e).map (fun v => fC'.eval [v])

/-- Distinctness, unpacked. -/
structure Ne8 (x e s s0 s1 c e0 e1 : Nat) : Prop where
  xe : x ≠ e
  xs : x ≠ s
  xs0 : x ≠ s0
  xs1 : x ≠ s1
  xc : x ≠ c
  xe0 : x ≠ e0
  xe1 : x ≠ e1
  es : e ≠ s
  es0 : e ≠ s0
  es1 : e ≠ s1
  ec : e ≠ c
  ee0 : e ≠ e0
  ee1 : e ≠ e1
  ss0 : s ≠ s0
  ss1 : s ≠ s1
  sc : s ≠ c
  se0 : s ≠ e0
  se1 : s ≠ e1
  s0s1 : s0 ≠ s1
  s0c : s0 ≠ c
  s0e0 : s0 ≠ e0
  s0e1 : s0 ≠ e1
  s1c : s1 ≠ c
  s1e0 : s1 ≠ e0
  s1e1 : s1 ≠ e1
  ce0 : c ≠ e0
  ce1 : c ≠ e1
  e0e1 : e0 ≠ e1

theorem ne8 (h : [x, e, s, s0, s1, c, e0, e1].Nodup) : Ne8 x e s s0 s1 c e0 e1 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false] at h
  constructor <;> intro hh <;> subst hh <;> simp_all

set_option hygiene false in
/-- Evaluate nested `upd`s at a channel, using every distinctness fact of `N`. -/
macro "nsimp" : tactic => `(tactic| simp [upd, N.xe, N.xs, N.xs0, N.xs1, N.xc, N.xe0, N.xe1, N.es, N.es0, N.es1,
  N.ec, N.ee0, N.ee1, N.ss0, N.ss1, N.sc, N.se0, N.se1, N.s0s1, N.s0c, N.s0e0, N.s0e1, N.s1c, N.s1e0, N.s1e1,
  N.ce0, N.ce1, N.e0e1, N.xe.symm, N.xs.symm, N.xs0.symm, N.xs1.symm, N.xc.symm, N.xe0.symm, N.xe1.symm,
  N.es.symm, N.es0.symm, N.es1.symm, N.ec.symm, N.ee0.symm, N.ee1.symm, N.ss0.symm, N.ss1.symm, N.sc.symm,
  N.se0.symm, N.se1.symm, N.s0s1.symm, N.s0c.symm, N.s0e0.symm, N.s0e1.symm, N.s1c.symm, N.s1e0.symm,
  N.s1e1.symm, N.ce0.symm, N.ce1.symm, N.e0e1.symm])

/-- The rewritten graph's flush: fork every `e` token, then drain `e0` and `e1`. -/
theorem flushB (P : Pat rs rs' a b d f x e s s0 s1 c e0 e1 fX fA fC fC') (σ : Store Nat Nat) :
    ∃ τ n, Run (step (graph rs')) σ n τ ∧ τ e = [] ∧ τ e0 = [] ∧ τ e1 = [] ∧
      τ s0 = σ s0 ++ (σ e0).map (fun v => fA.eval [v]) ++ (σ e).map (fun v => fA.eval [v]) ∧
      τ c = σ c ++ (σ e1).map (fun v => fC'.eval [v]) ++ (σ e).map (fun v => fC'.eval [v]) ∧
      ∀ ch, ch ≠ e → ch ≠ e0 → ch ≠ e1 → ch ≠ s0 → ch ≠ c → τ ch = σ ch := by
  have N := ne8 P.hnd
  obtain ⟨n1, r1⟩ := drain_fork2 P.hb' N.ee0 N.ee1 N.e0e1 (σ e) σ rfl
  let σ1 := upd (upd (upd σ e []) e0 (σ e0 ++ σ e)) e1 (σ e1 ++ σ e)
  obtain ⟨n2, r2⟩ := drain_comp1 P.hd' (Ne.symm N.s0e0) (σ1 e0) σ1 rfl
  let σ2 := upd (upd σ1 e0 []) s0 (σ1 s0 ++ (σ1 e0).map (fun v => fA.eval [v]))
  obtain ⟨n3, r3⟩ := drain_comp1 P.hf' (Ne.symm N.ce1) (σ2 e1) σ2 rfl
  refine ⟨_, _, run_trans r1 (run_trans r2 r3), ?_⟩
  simp only [σ2, σ1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · nsimp
  · nsimp
  · nsimp
  · nsimp
  · nsimp
  · intro ch h1 h2 h3 h4 h5; simp [upd, h1, h2, h3, h4, h5]

/-- The original graph's flush: drain `e` through the add, `s` through the fork, `s1` through the compare. -/
theorem flushA (P : Pat rs rs' a b d f x e s s0 s1 c e0 e1 fX fA fC fC') (σ : Store Nat Nat) :
    ∃ τ n, Run (step (graph rs)) σ n τ ∧ τ e = [] ∧ τ s = [] ∧ τ s1 = [] ∧
      τ s0 = σ s0 ++ σ s ++ (σ e).map (fun v => fA.eval [v]) ∧
      τ c = σ c ++ (σ s1).map (fun v => fC.eval [v]) ++ (σ s).map (fun v => fC.eval [v]) ++
        (σ e).map (fun v => fC.eval [fA.eval [v]]) ∧
      ∀ ch, ch ≠ e → ch ≠ s → ch ≠ s1 → ch ≠ s0 → ch ≠ c → τ ch = σ ch := by
  have N := ne8 P.hnd
  obtain ⟨n1, r1⟩ := drain_comp1 P.hb N.es (σ e) σ rfl
  let σ1 := upd (upd σ e []) s (σ s ++ (σ e).map (fun v => fA.eval [v]))
  obtain ⟨n2, r2⟩ := drain_fork2 P.hd N.ss0 N.ss1 N.s0s1 (σ1 s) σ1 rfl
  let σ2 := upd (upd (upd σ1 s []) s0 (σ1 s0 ++ σ1 s)) s1 (σ1 s1 ++ σ1 s)
  obtain ⟨n3, r3⟩ := drain_comp1 P.hf N.s1c (σ2 s1) σ2 rfl
  refine ⟨_, _, run_trans r1 (run_trans r2 r3), ?_⟩
  simp only [σ2, σ1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · nsimp
  · nsimp
  · nsimp
  · nsimp
  · nsimp
  · intro ch h1 h2 h3 h4 h5; simp [upd, h1, h2, h3, h4, h5]

/-! ## Firing an outside rule -/

theorem step_some_rule {rs : List Rule} {σ σ1 : Store Nat Nat} {l : Nat} (h : step (graph rs) σ l = some σ1) :
    ∃ r fr, rs[l]? = some r ∧ r.fire natVI σ = some fr ∧ σ1 = applyF σ fr := by
  cases hr : rs[l]? with
  | none => rw [step_graph_none hr] at h; cases h
  | some r =>
    rw [step_graph hr] at h
    cases hf : r.fire natVI σ with
    | none => rw [hf] at h; cases h
    | some fr => rw [hf] at h; cases h; exact ⟨r, fr, rfl, hf, rfl⟩

theorem applyF_keep {r : Rule} {σ : Store Nat Nat} {fr : Fire Nat Nat} (hf : r.fire natVI σ = some fr)
    {ch : Nat} (hi : ch ∉ r.insL) (ho : ch ∉ r.outsL) : applyF σ fr ch = σ ch := by
  have h1 := (r.node natVI).pop_ins σ fr ch hf hi
  have h2 := (r.node natVI).push_outs σ fr ch hf ho
  simp [applyF, h1, h2]

theorem applyF_noout {r : Rule} {σ : Store Nat Nat} {fr : Fire Nat Nat} (hf : r.fire natVI σ = some fr)
    {ch : Nat} (ho : ch ∉ r.outsL) : applyF σ fr ch = (σ ch).drop (fr.1 ch) := by
  have h2 := (r.node natVI).push_outs σ fr ch hf ho
  simp [applyF, h2]

theorem fire_le {r : Rule} {σ : Store Nat Nat} {fr : Fire Nat Nat} (hf : r.fire natVI σ = some fr) (ch : Nat) :
    fr.1 ch ≤ (σ ch).length := (r.node natVI).pop_le σ fr ch hf

theorem fire_mono {r : Rule} {σ τ : Store Nat Nat} {fr : Fire Nat Nat} (hf : r.fire natVI σ = some fr)
    (h : ∀ ch ∈ r.insL, ∃ y, τ ch = σ ch ++ y) : r.fire natVI τ = some fr :=
  (r.node natVI).mono σ τ fr hf h

theorem run_one {rs : List Rule} {σ τ : Store Nat Nat} {l : Nat} (h : step (graph rs) σ l = some τ) :
    Run (step (graph rs)) σ 1 τ := Run.cons l h (Run.refl τ)

/-! ## Forward: the original graph's steps, matched by the rewritten graph -/

theorem fwd_step (P : Pat rs rs' a b d f x e s s0 s1 c e0 e1 fX fA fC fC') :
    ∀ σ σ' l σ1, Rel x e s s0 s1 c e0 e1 fA fC fC' σ σ' → step (graph rs) σ l = some σ1 →
      ∃ σ1' n, Run (step (graph rs')) σ' n σ1' ∧ Rel x e s s0 s1 c e0 e1 fA fC fC' σ1 σ1' := by
  have N := ne8 P.hnd
  intro σ σ' l σ1 ⟨hR, h0, h1, h2, h3, hS0, hC⟩ hst
  by_cases la : l = a
  · subst la
    cases hx : σ x with
    | nil => rw [step_comp1_none P.ha hx] at hst; cases hst
    | cons v vs =>
      rw [step_comp1 P.ha N.xe hx] at hst; cases hst
      have hx' : σ' x = v :: vs := by rw [hR x N.xe N.xs N.xs1 N.xe0 N.xe1 N.xs0 N.xc, hx]
      refine ⟨_, 1, run_one (step_comp1 P.ha' N.xe hx'), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro ch k1 k2 k3 k4 k5 k6 k7
        by_cases kx : ch = x
        · subst kx; simp [upd, N.xe]
        · simp [upd, kx, k1, hR ch k1 k2 k3 k4 k5 k6 k7]
      · nsimp; exact h0
      · nsimp; exact h1
      · nsimp; exact h2
      · nsimp; exact h3
      · nsimp; simp only [← List.append_assoc]; rw [hS0]
      · nsimp; simp only [← List.append_assoc]; rw [hC, P.hH]
  by_cases lb : l = b
  · subst lb
    cases he : σ e with
    | nil => rw [step_comp1_none P.hb he] at hst; cases hst
    | cons v vs =>
      rw [step_comp1 P.hb N.es he] at hst; cases hst
      refine ⟨σ', 0, Run.refl _, ?_, ?_, ?_, h2, h3, ?_, ?_⟩
      · intro ch k1 k2 k3 k4 k5 k6 k7; simp [upd, k1, k2, hR ch k1 k2 k3 k4 k5 k6 k7]
      · nsimp; exact h0
      · nsimp; exact h1
      · nsimp; rw [he] at hS0; simpa using hS0
      · nsimp; rw [he] at hC; simpa using hC
  by_cases ld : l = d
  · subst ld
    cases hs : σ s with
    | nil => rw [step_fork2_none P.hd hs] at hst; cases hst
    | cons v vs =>
      rw [step_fork2 P.hd N.ss0 N.ss1 N.s0s1 hs] at hst; cases hst
      refine ⟨σ', 0, Run.refl _, ?_, ?_, ?_, h2, h3, ?_, ?_⟩
      · intro ch k1 k2 k3 k4 k5 k6 k7; simp [upd, k2, k3, k6, hR ch k1 k2 k3 k4 k5 k6 k7]
      · nsimp; exact h0
      · nsimp; exact h1
      · nsimp; rw [hs] at hS0; simpa using hS0
      · nsimp; rw [hs] at hC; simpa using hC
  by_cases lf : l = f
  · subst lf
    cases hs : σ s1 with
    | nil => rw [step_comp1_none P.hf hs] at hst; cases hst
    | cons v vs =>
      rw [step_comp1 P.hf N.s1c hs] at hst; cases hst
      refine ⟨σ', 0, Run.refl _, ?_, ?_, ?_, h2, h3, ?_, ?_⟩
      · intro ch k1 k2 k3 k4 k5 k6 k7; simp [upd, k3, k7, hR ch k1 k2 k3 k4 k5 k6 k7]
      · nsimp; exact h0
      · nsimp; exact h1
      · nsimp; simpa using hS0
      · nsimp; rw [hs] at hC; simpa using hC
  -- an outside rule: flush the rewritten graph, then fire it there
  obtain ⟨r, fr, hr, hf, rfl⟩ := step_some_rule hst
  have hin := P.hins l r la lb ld lf hr
  have hout := P.houts l r la lb ld lf hr
  obtain ⟨τ, n, hrun, t0, t1, t2, tS0, tC, tR⟩ := flushB P σ'
  have hfτ : r.fire natVI τ = some fr := by
    refine fire_mono hf ?_
    intro ch hch
    obtain ⟨k1, k2, k3, k4, k5⟩ := hin ch hch
    by_cases k6 : ch = s0
    · subst k6; exact ⟨_, by rw [tS0, ← hS0, List.append_assoc]⟩
    · by_cases k7 : ch = c
      · subst k7; exact ⟨_, by rw [tC, ← hC, List.append_assoc, List.append_assoc]⟩
      · exact ⟨[], by rw [List.append_nil, tR ch k1 k4 k5 k6 k7, hR ch k1 k2 k3 k4 k5 k6 k7]⟩
  have hst' : step (graph rs') τ l = some (applyF τ fr) := by
    rw [step_graph (by rw [P.hsame l la lb ld lf]; exact hr), hfτ]; rfl
  have nin : ∀ ch, (ch = e ∨ ch = s ∨ ch = s1 ∨ ch = e0 ∨ ch = e1) → ch ∉ r.insL := by
    intro ch hc hm; obtain ⟨k1, k2, k3, k4, k5⟩ := hin ch hm
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp_all
  have nout : ∀ ch, (ch = e ∨ ch = s ∨ ch = s1 ∨ ch = e0 ∨ ch = e1 ∨ ch = s0 ∨ ch = c) → ch ∉ r.outsL := by
    intro ch hc hm; obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hout ch hm
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  refine ⟨_, n + 1, run_trans hrun (run_one hst'), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ch k1 k2 k3 k4 k5 k6 k7
    simp only [applyF]; rw [tR ch k1 k4 k5 k6 k7, hR ch k1 k2 k3 k4 k5 k6 k7]
  · rw [applyF_keep hf (nin e0 (by simp)) (nout e0 (by simp)), h0]
  · rw [applyF_keep hf (nin e1 (by simp)) (nout e1 (by simp)), h1]
  · rw [applyF_noout hfτ (nout s (by simp)), tR s N.es.symm N.se0 N.se1 N.ss0 N.sc, h2]; simp
  · rw [applyF_noout hfτ (nout s1 (by simp)), tR s1 N.es1.symm N.s1e0 N.s1e1 N.s0s1.symm N.s1c, h3]; simp
  · rw [applyF_noout hf (nout s0 (by simp)), applyF_noout hfτ (nout s0 (by simp)),
      applyF_keep hf (nin s (by simp)) (nout s (by simp)), applyF_keep hf (nin e (by simp)) (nout e (by simp)),
      applyF_noout hfτ (nout e0 (by simp)), applyF_noout hfτ (nout e (by simp)), t0, tS0, ← hS0, t1]
    have k := fire_le hf s0
    simp [List.append_assoc, List.drop_append_of_le_length k]
  · rw [applyF_noout hf (nout c (by simp)), applyF_noout hfτ (nout c (by simp)),
      applyF_keep hf (nin s (by simp)) (nout s (by simp)), applyF_keep hf (nin e (by simp)) (nout e (by simp)),
      applyF_keep hf (nin s1 (by simp)) (nout s1 (by simp)),
      applyF_noout hfτ (nout e1 (by simp)), applyF_noout hfτ (nout e (by simp)), t0, tC, ← hC, t2]
    have k := fire_le hf c
    simp [List.append_assoc, List.drop_append_of_le_length k]

theorem term_comp1 {rs : List Rule} {l i o : Nat} {g : E} (hr : rs[l]? = some (.comp [i] o g)) (hio : i ≠ o)
    {σ : Store Nat Nat} (ht : Terminal (step (graph rs)) σ) : σ i = [] := by
  cases h : σ i with
  | nil => rfl
  | cons v vs => have := step_comp1 hr hio h; rw [ht l] at this; cases this

theorem term_fork2 {rs : List Rule} {l i o1 o2 : Nat} (hr : rs[l]? = some (.fork i [o1, o2]))
    (h1 : i ≠ o1) (h2 : i ≠ o2) (h12 : o1 ≠ o2)
    {σ : Store Nat Nat} (ht : Terminal (step (graph rs)) σ) : σ i = [] := by
  cases h : σ i with
  | nil => rfl
  | cons v vs => have := step_fork2 hr h1 h2 h12 h; rw [ht l] at this; cases this

/-- An outside rule disabled in `t` is disabled in `τ` if they agree on its inputs. -/
theorem other_none {rs rs' : List Rule} {l : Nat} (hs : rs'[l]? = rs[l]?) {t τ : Store Nat Nat}
    (ht : step (graph rs) t l = none)
    (hag : ∀ r, rs[l]? = some r → ∀ ch ∈ r.insL, τ ch = t ch) : step (graph rs') τ l = none := by
  cases hr : rs[l]? with
  | none => exact step_graph_none (by rw [hs, hr]) τ
  | some r =>
    rw [step_graph (by rw [hs, hr]), fire_congr r (hag r hr)]
    rw [step_graph hr] at ht
    cases h : r.fire natVI t with
    | none => rfl
    | some _ => rw [h] at ht; cases ht

theorem fwd_term (P : Pat rs rs' a b d f x e s s0 s1 c e0 e1 fX fA fC fC') :
    ∀ t σ', Rel x e s s0 s1 c e0 e1 fA fC fC' t σ' → Terminal (step (graph rs)) t →
      ∃ τ n, Run (step (graph rs')) σ' n τ ∧ Terminal (step (graph rs')) τ ∧
        ∀ ch, ch ≠ e → ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → τ ch = t ch := by
  have N := ne8 P.hnd
  intro t σ' ⟨hR, h0, h1, h2, h3, hS0, hC⟩ ht
  have tx := term_comp1 P.ha N.xe ht
  have te := term_comp1 P.hb N.es ht
  have ts := term_fork2 P.hd N.ss0 N.ss1 N.s0s1 ht
  have ts1 := term_comp1 P.hf N.s1c ht
  obtain ⟨τ, n, hrun, t0, t1, t2, tS0, tC, tR⟩ := flushB P σ'
  have agree : ∀ ch, ch ≠ e → ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → τ ch = t ch := by
    intro ch k1 k2 k3 k4 k5
    by_cases k6 : ch = s0
    · subst k6; rw [tS0, ← hS0, ts, te]; simp
    · by_cases k7 : ch = c
      · subst k7; rw [tC, ← hC, ts, te, ts1]; simp
      · rw [tR ch k1 k4 k5 k6 k7, hR ch k1 k2 k3 k4 k5 k6 k7]
  refine ⟨τ, n, hrun, ?_, agree⟩
  intro l
  by_cases la : l = a
  · subst la; exact step_comp1_none P.ha' (by rw [agree x N.xe N.xs N.xs1 N.xe0 N.xe1, tx])
  by_cases lb : l = b
  · subst lb; exact step_fork2_none P.hb' t0
  by_cases ld : l = d
  · subst ld; exact step_comp1_none P.hd' t1
  by_cases lf : l = f
  · subst lf; exact step_comp1_none P.hf' t2
  refine other_none (P.hsame l la lb ld lf) (ht l) ?_
  intro r hr ch hch
  obtain ⟨k1, k2, k3, k4, k5⟩ := P.hins l r la lb ld lf hr ch hch
  exact agree ch k1 k2 k3 k4 k5

/-! ## Backward: the rewritten graph's steps, matched by the original graph -/

theorem bwd_step (P : Pat rs rs' a b d f x e s s0 s1 c e0 e1 fX fA fC fC') :
    ∀ σ' σ l σ1', Rel x e s s0 s1 c e0 e1 fA fC fC' σ σ' → step (graph rs') σ' l = some σ1' →
      ∃ σ1 n, Run (step (graph rs)) σ n σ1 ∧ Rel x e s s0 s1 c e0 e1 fA fC fC' σ1 σ1' := by
  have N := ne8 P.hnd
  intro σ' σ l σ1' ⟨hR, h0, h1, h2, h3, hS0, hC⟩ hst
  by_cases la : l = a
  · subst la
    cases hx' : σ' x with
    | nil => rw [step_comp1_none P.ha' hx'] at hst; cases hst
    | cons v vs =>
      rw [step_comp1 P.ha' N.xe hx'] at hst; cases hst
      have hx : σ x = v :: vs := by rw [← hR x N.xe N.xs N.xs1 N.xe0 N.xe1 N.xs0 N.xc, hx']
      refine ⟨_, 1, run_one (step_comp1 P.ha N.xe hx), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro ch k1 k2 k3 k4 k5 k6 k7
        by_cases kx : ch = x
        · subst kx; simp [upd, N.xe]
        · simp [upd, kx, k1, hR ch k1 k2 k3 k4 k5 k6 k7]
      · nsimp; exact h0
      · nsimp; exact h1
      · nsimp; exact h2
      · nsimp; exact h3
      · nsimp; simp only [← List.append_assoc]; rw [hS0]
      · nsimp; simp only [← List.append_assoc]; rw [hC, P.hH]
  by_cases lb : l = b
  · subst lb
    cases he : σ' e with
    | nil => rw [step_fork2_none P.hb' he] at hst; cases hst
    | cons v vs =>
      rw [step_fork2 P.hb' N.ee0 N.ee1 N.e0e1 he] at hst; cases hst
      refine ⟨σ, 0, Run.refl _, ?_, h0, h1, ?_, ?_, ?_, ?_⟩
      · intro ch k1 k2 k3 k4 k5 k6 k7; simp [upd, k1, k4, k5, hR ch k1 k2 k3 k4 k5 k6 k7]
      · nsimp; exact h2
      · nsimp; exact h3
      · nsimp; rw [he] at hS0; simpa using hS0
      · nsimp; rw [he] at hC; simpa using hC
  by_cases ld : l = d
  · subst ld
    cases he : σ' e0 with
    | nil => rw [step_comp1_none P.hd' he] at hst; cases hst
    | cons v vs =>
      rw [step_comp1 P.hd' (Ne.symm N.s0e0) he] at hst; cases hst
      refine ⟨σ, 0, Run.refl _, ?_, h0, h1, ?_, ?_, ?_, ?_⟩
      · intro ch k1 k2 k3 k4 k5 k6 k7; simp [upd, k4, k6, hR ch k1 k2 k3 k4 k5 k6 k7]
      · nsimp; exact h2
      · nsimp; exact h3
      · nsimp; rw [he] at hS0; simpa using hS0
      · nsimp; simpa using hC
  by_cases lf : l = f
  · subst lf
    cases he : σ' e1 with
    | nil => rw [step_comp1_none P.hf' he] at hst; cases hst
    | cons v vs =>
      rw [step_comp1 P.hf' (Ne.symm N.ce1) he] at hst; cases hst
      refine ⟨σ, 0, Run.refl _, ?_, h0, h1, ?_, ?_, ?_, ?_⟩
      · intro ch k1 k2 k3 k4 k5 k6 k7; simp [upd, k5, k7, hR ch k1 k2 k3 k4 k5 k6 k7]
      · nsimp; exact h2
      · nsimp; exact h3
      · nsimp; simpa using hS0
      · nsimp; rw [he] at hC; simpa using hC
  -- an outside rule: flush the original graph, then fire it there
  obtain ⟨r, fr, hr', hf, rfl⟩ := step_some_rule hst
  have hr : rs[l]? = some r := by rw [← P.hsame l la lb ld lf]; exact hr'
  have hin := P.hins l r la lb ld lf hr
  have hout := P.houts l r la lb ld lf hr
  obtain ⟨τ, n, hrun, t0, t1, t2, tS0, tC, tR⟩ := flushA P σ
  have hfτ : r.fire natVI τ = some fr := by
    refine fire_mono hf ?_
    intro ch hch
    obtain ⟨k1, k2, k3, k4, k5⟩ := hin ch hch
    by_cases k6 : ch = s0
    · subst k6; exact ⟨_, by rw [tS0, hS0, List.append_assoc]⟩
    · by_cases k7 : ch = c
      · subst k7; exact ⟨_, by rw [tC, hC, List.append_assoc]⟩
      · exact ⟨[], by rw [List.append_nil, tR ch k1 k2 k3 k6 k7, hR ch k1 k2 k3 k4 k5 k6 k7]⟩
  have hst' : step (graph rs) τ l = some (applyF τ fr) := by
    rw [step_graph hr, hfτ]; rfl
  have nin : ∀ ch, (ch = e ∨ ch = s ∨ ch = s1 ∨ ch = e0 ∨ ch = e1) → ch ∉ r.insL := by
    intro ch hc hm; obtain ⟨k1, k2, k3, k4, k5⟩ := hin ch hm
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp_all
  have nout : ∀ ch, (ch = e ∨ ch = s ∨ ch = s1 ∨ ch = e0 ∨ ch = e1 ∨ ch = s0 ∨ ch = c) → ch ∉ r.outsL := by
    intro ch hc hm; obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hout ch hm
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  refine ⟨_, n + 1, run_trans hrun (run_one hst'), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ch k1 k2 k3 k4 k5 k6 k7
    simp only [applyF]; rw [tR ch k1 k2 k3 k6 k7, hR ch k1 k2 k3 k4 k5 k6 k7]
  · rw [applyF_noout hfτ (nout e0 (by simp)), tR e0 N.ee0.symm N.se0.symm N.s1e0.symm N.s0e0.symm N.ce0.symm, h0]
    simp
  · rw [applyF_noout hfτ (nout e1 (by simp)), tR e1 N.ee1.symm N.se1.symm N.s1e1.symm N.s0e1.symm N.ce1.symm, h1]
    simp
  · rw [applyF_keep hf (nin s (by simp)) (nout s (by simp)), h2]
  · rw [applyF_keep hf (nin s1 (by simp)) (nout s1 (by simp)), h3]
  · rw [applyF_noout hfτ (nout s0 (by simp)), applyF_noout hf (nout s0 (by simp)),
      applyF_noout hfτ (nout s (by simp)), applyF_noout hfτ (nout e (by simp)),
      applyF_keep hf (nin e0 (by simp)) (nout e0 (by simp)), applyF_keep hf (nin e (by simp)) (nout e (by simp)),
      t0, t1, tS0, hS0]
    have k := fire_le hf s0
    simp [List.append_assoc, List.drop_append_of_le_length k]
  · rw [applyF_noout hfτ (nout c (by simp)), applyF_noout hf (nout c (by simp)),
      applyF_noout hfτ (nout s (by simp)), applyF_noout hfτ (nout e (by simp)),
      applyF_noout hfτ (nout s1 (by simp)),
      applyF_keep hf (nin e1 (by simp)) (nout e1 (by simp)), applyF_keep hf (nin e (by simp)) (nout e (by simp)),
      t0, t1, t2, tC, hC]
    have k := fire_le hf c
    simp [List.append_assoc, List.drop_append_of_le_length k]

theorem bwd_term (P : Pat rs rs' a b d f x e s s0 s1 c e0 e1 fX fA fC fC') :
    ∀ t' σ, Rel x e s s0 s1 c e0 e1 fA fC fC' σ t' → Terminal (step (graph rs')) t' →
      ∃ τ n, Run (step (graph rs)) σ n τ ∧ Terminal (step (graph rs)) τ ∧
        ∀ ch, ch ≠ e → ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → τ ch = t' ch := by
  have N := ne8 P.hnd
  intro t' σ ⟨hR, h0, h1, h2, h3, hS0, hC⟩ ht
  have tx := term_comp1 P.ha' N.xe ht
  have te := term_fork2 P.hb' N.ee0 N.ee1 N.e0e1 ht
  have te0 := term_comp1 P.hd' (Ne.symm N.s0e0) ht
  have te1 := term_comp1 P.hf' (Ne.symm N.ce1) ht
  obtain ⟨τ, n, hrun, t0, t1, t2, tS0, tC, tR⟩ := flushA P σ
  have agree : ∀ ch, ch ≠ e → ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → τ ch = t' ch := by
    intro ch k1 k2 k3 k4 k5
    by_cases k6 : ch = s0
    · subst k6; rw [tS0, hS0, te, te0]; simp
    · by_cases k7 : ch = c
      · subst k7; rw [tC, hC, te, te1]; simp
      · rw [tR ch k1 k2 k3 k6 k7, hR ch k1 k2 k3 k4 k5 k6 k7]
  refine ⟨τ, n, hrun, ?_, agree⟩
  intro l
  by_cases la : l = a
  · subst la; exact step_comp1_none P.ha (by rw [agree x N.xe N.xs N.xs1 N.xe0 N.xe1, tx])
  by_cases lb : l = b
  · subst lb; exact step_comp1_none P.hb t0
  by_cases ld : l = d
  · subst ld; exact step_fork2_none P.hd t1
  by_cases lf : l = f
  · subst lf; exact step_comp1_none P.hf t2
  refine other_none (P.hsame l la lb ld lf).symm (ht l) ?_
  intro r hr ch hch
  have hr0 : rs[l]? = some r := by rw [← P.hsame l la lb ld lf]; exact hr
  obtain ⟨k1, k2, k3, k4, k5⟩ := P.hins l r la lb ld lf hr0 ch hch
  exact agree ch k1 k2 k3 k4 k5

/-! ## The theorems -/

/-- Every complete run of the original graph, from a store with empty internal channels, is matched by a
complete run of the rewritten graph ending in the same store outside the five internal channels. -/
theorem forward (P : Pat rs rs' a b d f x e s s0 s1 c e0 e1 fX fA fC fC') {σ0 t : Store Nat Nat} {n : Nat}
    (h0 : σ0 e = [] ∧ σ0 s = [] ∧ σ0 s1 = [] ∧ σ0 e0 = [] ∧ σ0 e1 = [])
    (hr : Run (step (graph rs)) σ0 n t) (ht : Terminal (step (graph rs)) t) :
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧
      ∀ ch, ch ≠ e → ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → t' ch = t ch := by
  obtain ⟨he, hs, hs1, he0, he1⟩ := h0
  exact sim_complete (Rel x e s s0 s1 c e0 e1 fA fC fC')
    (fun t t' => ∀ ch, ch ≠ e → ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → t' ch = t ch)
    (fwd_step P) (fwd_term P) hr ht σ0
    ⟨fun _ _ _ _ _ _ _ _ => rfl, he0, he1, hs, hs1, by simp [he, hs, he0], by simp [he, hs, hs1, he1]⟩

/-- Every complete run of the rewritten graph is matched by one of the original graph, ending in the same
store outside the five internal channels. -/
theorem backward (P : Pat rs rs' a b d f x e s s0 s1 c e0 e1 fX fA fC fC') {σ0 t' : Store Nat Nat} {n : Nat}
    (h0 : σ0 e = [] ∧ σ0 s = [] ∧ σ0 s1 = [] ∧ σ0 e0 = [] ∧ σ0 e1 = [])
    (hr : Run (step (graph rs')) σ0 n t') (ht : Terminal (step (graph rs')) t') :
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧
      ∀ ch, ch ≠ e → ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → t ch = t' ch := by
  obtain ⟨he, hs, hs1, he0, he1⟩ := h0
  exact sim_complete (fun σ' σ => Rel x e s s0 s1 c e0 e1 fA fC fC' σ σ')
    (fun t' t => ∀ ch, ch ≠ e → ch ≠ s → ch ≠ s1 → ch ≠ e0 → ch ≠ e1 → t ch = t' ch)
    (bwd_step P) (bwd_term P) hr ht σ0
    ⟨fun _ _ _ _ _ _ _ _ => rfl, he0, he1, hs, hs1, by simp [he, hs, he0], by simp [he, hs, hs1, he1]⟩

end Pattern

end Formal.Rewrite.IncCmp
