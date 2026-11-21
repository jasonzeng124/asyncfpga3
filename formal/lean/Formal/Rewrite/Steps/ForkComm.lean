import Formal.Rewrite.Steps.Basic

/-!
# Formal.Rewrite.Steps.ForkComm — a fork after a comp is a fork before two copies of it (shard A, 2026-11-19)

**Problem, plainly.** A comp computes `y = G(x)` and a fork copies `y` onto `y0` and `y1`. Is that the same, whatever
surrounds it, as a fork copying `x` onto `x0` and `x1`, followed by `y0 = G(x0)` and `y1 = G(x1)`? This is what lets
a loop test that reads the loop's UPDATE read the loop's VALUE instead (pre_eq2): the test's copy of the update can
then be folded into the test (`Absorb`).

**Proved** (`fc_forward`, `fc_backward`): for ANY imported graph `rs` holding `comp [x] y G` at `lc` and
`fork y [y0, y1]` at `lf`, and `rs'` equal except `fork x [x0, x1]` at `lc`, `comp [x0] y0 G` at `lf` and
`comp [x1] y1 G` at a label `le` unused in `rs`, with `x, y, x0, x1, y0, y1` distinct, no other rule reading `x, y,
x0, x1`, and no other rule writing `y, x0, x1, y0, y1`: from any store with `y, x0, x1` empty, every complete run of
either graph is matched by a complete run of the other ending in the same store outside `y, x0, x1`.

**Not covered:** token level only.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

structure PatFC (rs rs' : List Rule) (lc lf le x y x0 x1 y0 y1 : Nat) (G : E) : Prop where
  hc : rs[lc]? = some (.comp [x] y G)
  hf : rs[lf]? = some (.fork y [y0, y1])
  he : rs[le]? = none
  hc' : rs'[lc]? = some (.fork x [x0, x1])
  hf' : rs'[lf]? = some (.comp [x0] y0 G)
  he' : rs'[le]? = some (.comp [x1] y1 G)
  hsame : ∀ l, l ≠ lc → l ≠ lf → l ≠ le → rs'[l]? = rs[l]?
  hins : ∀ l r, l ≠ lc → l ≠ lf → rs[l]? = some r → ∀ c ∈ r.insL, c ∉ [x, y, x0, x1]
  houts : ∀ l r, l ≠ lc → l ≠ lf → rs[l]? = some r → ∀ c ∈ r.outsL, c ∉ [y, x0, x1, y0, y1]
  hnd : [x, y, x0, x1, y0, y1].Nodup

section FC
variable {rs rs' : List Rule} {lc lf le x y x0 x1 y0 y1 : Nat} {G : E}

def gm (G : E) (L : List Nat) : List Nat := L.map (fun v => G.eval [v])

/-- `σ` runs `rs`, `σ'` runs `rs'`. In `rs` the values not yet forked wait on `y`; in `rs'` the values not yet
computed wait on `x0` / `x1`. -/
def RelFC (y x0 x1 y0 y1 : Nat) (G : E) (σ σ' : Store Nat Nat) : Prop :=
  Agree [y, x0, x1, y0, y1] σ σ' ∧ σ x0 = [] ∧ σ x1 = [] ∧ σ' y = [] ∧
    σ y0 ++ σ y = σ' y0 ++ gm G (σ' x0) ∧ σ y1 ++ σ y = σ' y1 ++ gm G (σ' x1)

theorem PatFC.lcf (P : PatFC rs rs' lc lf le x y x0 x1 y0 y1 G) : lc ≠ lf := fun h => by
  have := P.hc; rw [h, P.hf] at this; cases this
theorem PatFC.lce (P : PatFC rs rs' lc lf le x y x0 x1 y0 y1 G) : lc ≠ le := fun h => by
  have := P.hc; rw [h, P.he] at this; cases this
theorem PatFC.lfe (P : PatFC rs rs' lc lf le x y x0 x1 y0 y1 G) : lf ≠ le := fun h => by
  have := P.hf; rw [h, P.he] at this; cases this

theorem PatFC.ne (P : PatFC rs rs' lc lf le x y x0 x1 y0 y1 G) :
    x ≠ y ∧ x ≠ x0 ∧ x ≠ x1 ∧ x ≠ y0 ∧ x ≠ y1 ∧ y ≠ x0 ∧ y ≠ x1 ∧ y ≠ y0 ∧ y ≠ y1 ∧
    x0 ≠ x1 ∧ x0 ≠ y0 ∧ x0 ≠ y1 ∧ x1 ≠ y0 ∧ x1 ≠ y1 ∧ y0 ≠ y1 := by
  have h := P.hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  omega

/-- The other rules: same in both graphs. -/
theorem PatFC.same (P : PatFC rs rs' lc lf le x y x0 x1 y0 y1 G) {l : Nat} (h1 : l ≠ lc) (h2 : l ≠ lf)
    (h3 : l ≠ le) : rs'[l]? = rs[l]? := P.hsame l h1 h2 h3

theorem notD {y x0 x1 y0 y1 c : Nat} (h : c ∉ [y, x0, x1, y0, y1]) :
    c ≠ y ∧ c ≠ x0 ∧ c ≠ x1 ∧ c ≠ y0 ∧ c ≠ y1 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h; exact h

/-- Drain both copies of `G` in `rs'`. -/
theorem fc_drain (P : PatFC rs rs' lc lf le x y x0 x1 y0 y1 G) {σ σ' : Store Nat Nat}
    (hR : RelFC y x0 x1 y0 y1 G σ σ') :
    ∃ n τ, Run (step (graph rs')) σ' n τ ∧ RelFC y x0 x1 y0 y1 G σ τ ∧ τ x0 = [] ∧ τ x1 = [] ∧
      τ y0 = σ y0 ++ σ y ∧ τ y1 = σ y1 ++ σ y := by
  obtain ⟨n_x_y, n_x_x0, n_x_x1, n_x_y0, n_x_y1, n_y_x0, n_y_x1, n_y_y0, n_y_y1, n_x0_x1, n_x0_y0, n_x0_y1, n_x1_y0, n_x1_y1, n_y0_y1⟩ := P.ne
  obtain ⟨hA, h0, h1, hy', hy0, hy1⟩ := hR
  obtain ⟨n1, r1⟩ := drain_comp1f P.hf' n_x0_y0 (σ' x0) σ' rfl
  obtain ⟨n2, r2⟩ := drain_comp1f P.he' n_x1_y1 _ _ rfl
  refine ⟨n1 + n2, _, run_trans r1 r2, ⟨?_, h0, h1, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨c1, c2, c3, c4, c5⟩ := notD hc
    simp only [c2, c3, c4, c5, ite_false]; exact hA c hc
  · simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, hy']
  · simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, gm, hy0]
  · simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, gm, hy1]
  · simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]
  · simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]
  · simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, gm, hy0]
  · simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, gm, hy1]

theorem fc_fwd_step (P : PatFC rs rs' lc lf le x y x0 x1 y0 y1 G) :
    ∀ σ σ' l u, RelFC y x0 x1 y0 y1 G σ σ' → step (graph rs) σ l = some u →
      ∃ u' n, Run (step (graph rs')) σ' n u' ∧ RelFC y x0 x1 y0 y1 G u u' := by
  intro σ σ' l u hR hs
  obtain ⟨n_x_y, n_x_x0, n_x_x1, n_x_y0, n_x_y1, n_y_x0, n_y_x1, n_y_y0, n_y_y1, n_x0_x1, n_x0_y0, n_x0_y1, n_x1_y0, n_x1_y1, n_y0_y1⟩ := P.ne
  obtain ⟨hA, h0, h1, hy', hy0, hy1⟩ := hR
  have hxx : σ' x = σ x := hA x (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])
  by_cases e1 : l = lc
  · rw [e1, step_graph P.hc] at hs
    cases hxv : σ x with
    | nil => rw [fire_comp_none (List.mem_singleton_self x) hxv] at hs; cases hs
    | cons v vs =>
      rw [fire_comp (by intro c hc; simp at hc; subst hc; rw [hxv]; simp)] at hs
      have hu := (Option.some.inj hs).symm
      subst hu
      have hs' : step (graph rs') σ' lc = some (applyF σ' (popOf [x], fun c => if c ∈ [x0, x1] then [v] else [])) := by
        rw [step_graph P.hc', fire_fork (by rw [hxx, hxv])]; rfl
      refine ⟨_, 1, Run.cons lc hs' (Run.refl _), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro c hc
        obtain ⟨c1, c2, c3, c4, c5⟩ := notD hc
        rw [comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]
        by_cases cx : c = x
        · subst cx; simp [hxx]
        · simp [cx, c1, c2, c3, hA c hc]
      · rw [comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, h0]
      · rw [comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, h1]
      · rw [fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, hy']
      · rw [comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]
        simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, gm, hd, hxv] at hy0 ⊢; rw [← List.append_assoc, hy0, List.append_assoc]
      · rw [comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]
        simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, gm, hd, hxv] at hy1 ⊢; rw [← List.append_assoc, hy1, List.append_assoc]
  · by_cases e2 : l = lf
    · rw [e2, step_graph P.hf] at hs
      cases hyv : σ y with
      | nil => rw [fire_fork_none hyv] at hs; cases hs
      | cons w ws =>
        rw [fire_fork hyv] at hs
        have hu := (Option.some.inj hs).symm
        subst hu
        refine ⟨σ', 0, Run.refl _, ?_, ?_, ?_, hy', ?_, ?_⟩
        · intro c hc
          obtain ⟨c1, c2, c3, c4, c5⟩ := notD hc
          rw [fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [c1, c4, c5, hA c hc]
        · rw [fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, h0]
        · rw [fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, h1]
        · rw [fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, hyv] at hy0 ⊢; exact hy0
        · rw [fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, hyv] at hy1 ⊢; exact hy1
    · have e3 : l ≠ le := fun h => by rw [h, none_none P.he] at hs; cases hs
      cases hr : rs[l]? with
      | none => rw [none_none hr] at hs; cases hs
      | some r =>
        have hr' : rs'[l]? = some r := by rw [P.same e1 e2 e3, hr]
        have hrd := P.hins l r e1 e2 hr
        have hro := P.houts l r e1 e2 hr
        obtain ⟨n, τ, hrun, ⟨hAτ, -, -, hyτ, -, -⟩, hτx0, hτx1, hτy0, hτy1⟩ := fc_drain P ⟨hA, h0, h1, hy', hy0, hy1⟩
        have hext : ∀ c ∈ r.insL, ∃ z, τ c = σ c ++ z := by
          intro c hc
          by_cases a0 : c = y0
          · subst a0; exact ⟨_, hτy0⟩
          · by_cases a1 : c = y1
            · subst a1; exact ⟨_, hτy1⟩
            · have hcD := hrd c hc
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hcD
              exact ⟨[], by rw [List.append_nil]; exact hAτ c (by simp [hcD.2.1, hcD.2.2.1, hcD.2.2.2, a0, a1])⟩
        obtain ⟨fr, hf, hfτ, rfl, hsτ⟩ := outside_step_ext hr' hr hext hs
        have nin : ∀ c, c ∈ [x, y, x0, x1] → c ∉ r.insL := fun c hc h => hrd c h hc
        have nout : ∀ c, c ∈ [y, x0, x1, y0, y1] → fr.2 c = [] := fun c hc => fire_push0 hf (fun h => hro c h hc)
        refine ⟨_, n + 1, run_trans hrun (Run.cons l hsτ (Run.refl _)), applyF_agree hAτ fr, ?_, ?_, ?_, ?_, ?_⟩
        · rw [applyF_app hf (nin x0 (by simp)), nout x0 (by simp), h0]; rfl
        · rw [applyF_app hf (nin x1 (by simp)), nout x1 (by simp), h1]; rfl
        · rw [applyF_app hfτ (nin y (by simp)), nout y (by simp), hyτ]; rfl
        · have hle : fr.1 y0 ≤ (σ y0).length := (r.node natVI).pop_le σ fr y0 hf
          have a1 : applyF σ fr y = σ y := by rw [applyF_app hf (nin y (by simp)), nout y (by simp), List.append_nil]
          have a2 : applyF τ fr x0 = [] := by rw [applyF_app hfτ (nin x0 (by simp)), nout x0 (by simp), hτx0]; rfl
          have a3 : applyF σ fr y0 = (σ y0).drop (fr.1 y0) := by rw [applyF_at, nout y0 (by simp), List.append_nil]
          have a4 : applyF τ fr y0 = (σ y0).drop (fr.1 y0) ++ σ y := by
            rw [applyF_at, nout y0 (by simp), List.append_nil, hτy0, drop_app_of_le hle]
          rw [a1, a2, a3, a4]; simp [gm]
        · have hle : fr.1 y1 ≤ (σ y1).length := (r.node natVI).pop_le σ fr y1 hf
          have a1 : applyF σ fr y = σ y := by rw [applyF_app hf (nin y (by simp)), nout y (by simp), List.append_nil]
          have a2 : applyF τ fr x1 = [] := by rw [applyF_app hfτ (nin x1 (by simp)), nout x1 (by simp), hτx1]; rfl
          have a3 : applyF σ fr y1 = (σ y1).drop (fr.1 y1) := by rw [applyF_at, nout y1 (by simp), List.append_nil]
          have a4 : applyF τ fr y1 = (σ y1).drop (fr.1 y1) ++ σ y := by
            rw [applyF_at, nout y1 (by simp), List.append_nil, hτy1, drop_app_of_le hle]
          rw [a1, a2, a3, a4]; simp [gm]

theorem fc_fwd_term (P : PatFC rs rs' lc lf le x y x0 x1 y0 y1 G) :
    ∀ σ σ', RelFC y x0 x1 y0 y1 G σ σ' → Terminal (step (graph rs)) σ →
      ∃ u' n, Run (step (graph rs')) σ' n u' ∧ Terminal (step (graph rs')) u' ∧ Agree [y, x0, x1] σ u' := by
  intro σ σ' hR hT
  obtain ⟨n_x_y, n_x_x0, n_x_x1, n_x_y0, n_x_y1, n_y_x0, n_y_x1, n_y_y0, n_y_y1, n_x0_x1, n_x0_y0, n_x0_y1, n_x1_y0, n_x1_y1, n_y0_y1⟩ := P.ne
  have hx0 : σ x = [] := by
    cases hxv : σ x with
    | nil => rfl
    | cons v vs =>
      have := hT lc
      rw [step_graph P.hc, fire_comp (by intro c hc; simp at hc; subst hc; rw [hxv]; simp)] at this; cases this
  have hy0e : σ y = [] := by
    cases hyv : σ y with
    | nil => rfl
    | cons v vs => have := hT lf; rw [step_graph P.hf, fire_fork hyv] at this; cases this
  obtain ⟨n, τ, hrun, ⟨hAτ, h0, h1, hyτ, -, -⟩, hτx0, hτx1, hτy0, hτy1⟩ := fc_drain P hR
  have heq : τ = σ := by
    funext c
    by_cases a : c ∈ [y, x0, x1, y0, y1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at a
      rcases a with rfl | rfl | rfl | rfl | rfl
      · rw [hyτ, hy0e]
      · rw [hτx0, h0]
      · rw [hτx1, h1]
      · rw [hτy0, hy0e, List.append_nil]
      · rw [hτy1, hy0e, List.append_nil]
    · exact hAτ c a
  subst heq
  refine ⟨τ, n, hrun, ?_, fun _ _ => rfl⟩
  intro l
  by_cases e1 : l = lc
  · rw [e1, step_graph P.hc', fire_fork_none hx0]; rfl
  · by_cases e2 : l = lf
    · rw [e2, step_graph P.hf', fire_comp_none (List.mem_singleton_self x0) hτx0]; rfl
    · by_cases e3 : l = le
      · rw [e3, step_graph P.he', fire_comp_none (List.mem_singleton_self x1) hτx1]; rfl
      · have := hT l
        cases hr : rs[l]? with
        | none => have hr' : rs'[l]? = none := by rw [P.same e1 e2 e3, hr]
                  exact none_none hr' τ
        | some r =>
          have hr' : rs'[l]? = some r := by rw [P.same e1 e2 e3, hr]
          rw [step_graph hr] at this; rw [step_graph hr', this]

theorem fc_bwd_step (P : PatFC rs rs' lc lf le x y x0 x1 y0 y1 G) :
    ∀ σ' σ l u', RelFC y x0 x1 y0 y1 G σ σ' → step (graph rs') σ' l = some u' →
      ∃ u n, Run (step (graph rs)) σ n u ∧ RelFC y x0 x1 y0 y1 G u u' := by
  intro σ' σ l u' hR hs
  obtain ⟨n_x_y, n_x_x0, n_x_x1, n_x_y0, n_x_y1, n_y_x0, n_y_x1, n_y_y0, n_y_y1, n_x0_x1, n_x0_y0, n_x0_y1, n_x1_y0, n_x1_y1, n_y0_y1⟩ := P.ne
  obtain ⟨hA, h0, h1, hy', hy0, hy1⟩ := hR
  have hxx : σ' x = σ x := hA x (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])
  by_cases e1 : l = lc
  · rw [e1, step_graph P.hc'] at hs
    cases hxv' : σ' x with
    | nil => rw [fire_fork_none hxv'] at hs; cases hs
    | cons v vs =>
      rw [fire_fork hxv'] at hs
      have hu' := (Option.some.inj hs).symm
      subst hu'
      have hxv : σ x = v :: vs := by rw [← hxx, hxv']
      have hs1 : step (graph rs) σ lc = some (applyF σ (popOf [x],
          fun c => if c = y then [G.eval ([x].map (hd σ))] else [])) := by
        rw [step_graph P.hc, fire_comp (by intro c hc; simp at hc; subst hc; rw [hxv]; simp)]; rfl
      refine ⟨_, 1, Run.cons lc hs1 (Run.refl _), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro c hc
        obtain ⟨c1, c2, c3, c4, c5⟩ := notD hc
        rw [comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]
        by_cases cx : c = x
        · subst cx; simp [hxx]
        · simp [cx, c1, c2, c3, hA c hc]
      · rw [comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, h0]
      · rw [comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, h1]
      · rw [fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, hy']
      · rw [comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]
        simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, gm, hd, hxv] at hy0 ⊢; rw [← List.append_assoc, hy0, List.append_assoc]
      · rw [comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]), fork_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]
        simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, gm, hd, hxv] at hy1 ⊢; rw [← List.append_assoc, hy1, List.append_assoc]
  · by_cases e2 : l = lf
    · rw [e2, step_graph P.hf'] at hs
      cases hv : σ' x0 with
      | nil => rw [fire_comp_none (List.mem_singleton_self x0) hv] at hs; cases hs
      | cons v vs =>
        rw [fire_comp (by intro c hc; simp at hc; subst hc; rw [hv]; simp)] at hs
        have hu' := (Option.some.inj hs).symm
        subst hu'
        refine ⟨σ, 0, Run.refl _, ?_, h0, h1, ?_, ?_, ?_⟩
        · intro c hc
          obtain ⟨c1, c2, c3, c4, c5⟩ := notD hc
          rw [comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [c2, c4, hA c hc]
        · rw [comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, hy']
        · simp only [comp_at (ins := [x0]) (o := y0) (F := G) (σ := σ') (by simp [n_x0_y0.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, gm, hd, hv] at hy0 ⊢; exact hy0
        · simp only [comp_at (ins := [x0]) (o := y0) (F := G) (σ := σ') (by simp [n_x0_y0.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm] at hy1 ⊢; exact hy1
    · by_cases e3 : l = le
      · rw [e3, step_graph P.he'] at hs
        cases hv : σ' x1 with
        | nil => rw [fire_comp_none (List.mem_singleton_self x1) hv] at hs; cases hs
        | cons v vs =>
          rw [fire_comp (by intro c hc; simp at hc; subst hc; rw [hv]; simp)] at hs
          have hu' := (Option.some.inj hs).symm
          subst hu'
          refine ⟨σ, 0, Run.refl _, ?_, h0, h1, ?_, ?_, ?_⟩
          · intro c hc
            obtain ⟨c1, c2, c3, c4, c5⟩ := notD hc
            rw [comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [c3, c5, hA c hc]
          · rw [comp_at (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, hy']
          · simp only [comp_at (ins := [x1]) (o := y1) (F := G) (σ := σ') (by simp [n_x1_y1.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm] at hy0 ⊢; exact hy0
          · simp only [comp_at (ins := [x1]) (o := y1) (F := G) (σ := σ') (by simp [n_x1_y1.symm])]; simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, gm, hd, hv] at hy1 ⊢; exact hy1
      · cases hr' : rs'[l]? with
        | none => rw [none_none hr'] at hs; cases hs
        | some r =>
          have hr : rs[l]? = some r := by rw [← P.same e1 e2 e3, hr']
          have hrd := P.hins l r e1 e2 hr
          have hro := P.houts l r e1 e2 hr
          -- drain the fork of y in rs
          obtain ⟨n, hrun⟩ := drain_fork P.hf (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]) (σ y) σ rfl
          let τ : Store Nat Nat := fun c => if c = y then [] else if c ∈ [y0, y1] then σ c ++ σ y else σ c
          have hτy0 : τ y0 = σ' y0 ++ gm G (σ' x0) := by simp [τ, n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]; exact hy0
          have hτy1 : τ y1 = σ' y1 ++ gm G (σ' x1) := by simp [τ, n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]; exact hy1
          have hAτ : Agree [y, x0, x1, y0, y1] τ σ' := by
            intro c hc
            obtain ⟨c1, c2, c3, c4, c5⟩ := notD hc
            simp [τ, c1, c4, c5]; exact hA c hc
          have hext : ∀ c ∈ r.insL, ∃ z, τ c = σ' c ++ z := by
            intro c hc
            by_cases a0 : c = y0
            · subst a0; exact ⟨_, hτy0⟩
            · by_cases a1 : c = y1
              · subst a1; exact ⟨_, hτy1⟩
              · have hcD := hrd c hc
                simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hcD
                exact ⟨[], by rw [List.append_nil]; exact (hAτ c (by simp [hcD.2.1, hcD.2.2.1, hcD.2.2.2, a0, a1])).symm⟩
          obtain ⟨fr, hf', hfτ, rfl, hsτ⟩ := outside_step_ext hr hr' hext hs
          have nin : ∀ c, c ∈ [x, y, x0, x1] → c ∉ r.insL := fun c hc h => hrd c h hc
          have nout : ∀ c, c ∈ [y, x0, x1, y0, y1] → fr.2 c = [] := fun c hc => fire_push0 hf' (fun h => hro c h hc)
          refine ⟨_, n + 1, run_trans hrun (Run.cons l hsτ (Run.refl _)), (applyF_agree hAτ fr).symm.symm, ?_, ?_, ?_, ?_, ?_⟩
          · rw [applyF_app hfτ (nin x0 (by simp)), nout x0 (by simp)]; simp [τ, n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, h0]
          · rw [applyF_app hfτ (nin x1 (by simp)), nout x1 (by simp)]; simp [τ, n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, h1]
          · rw [applyF_app hf' (nin y (by simp)), nout y (by simp), hy']; rfl
          · have hle : fr.1 y0 ≤ (σ' y0).length := (r.node natVI).pop_le σ' fr y0 hf'
            have a1 : applyF τ fr y = [] := by
              rw [applyF_app hfτ (nin y (by simp)), nout y (by simp)]; simp [τ]
            have a2 : applyF σ' fr x0 = σ' x0 := by
              rw [applyF_app hf' (nin x0 (by simp)), nout x0 (by simp), List.append_nil]
            have a3 : applyF σ' fr y0 = (σ' y0).drop (fr.1 y0) := by rw [applyF_at, nout y0 (by simp), List.append_nil]
            have a4 : applyF τ fr y0 = (σ' y0).drop (fr.1 y0) ++ gm G (σ' x0) := by
              rw [applyF_at, nout y0 (by simp), List.append_nil, hτy0, drop_app_of_le hle]
            rw [a1, a2, a3, a4, List.append_nil]
          · have hle : fr.1 y1 ≤ (σ' y1).length := (r.node natVI).pop_le σ' fr y1 hf'
            have a1 : applyF τ fr y = [] := by
              rw [applyF_app hfτ (nin y (by simp)), nout y (by simp)]; simp [τ]
            have a2 : applyF σ' fr x1 = σ' x1 := by
              rw [applyF_app hf' (nin x1 (by simp)), nout x1 (by simp), List.append_nil]
            have a3 : applyF σ' fr y1 = (σ' y1).drop (fr.1 y1) := by rw [applyF_at, nout y1 (by simp), List.append_nil]
            have a4 : applyF τ fr y1 = (σ' y1).drop (fr.1 y1) ++ gm G (σ' x1) := by
              rw [applyF_at, nout y1 (by simp), List.append_nil, hτy1, drop_app_of_le hle]
            rw [a1, a2, a3, a4, List.append_nil]

theorem fc_bwd_term (P : PatFC rs rs' lc lf le x y x0 x1 y0 y1 G) :
    ∀ σ' σ, RelFC y x0 x1 y0 y1 G σ σ' → Terminal (step (graph rs')) σ' →
      ∃ u n, Run (step (graph rs)) σ n u ∧ Terminal (step (graph rs)) u ∧ Agree [y, x0, x1] σ' u := by
  intro σ' σ hR hT
  obtain ⟨n_x_y, n_x_x0, n_x_x1, n_x_y0, n_x_y1, n_y_x0, n_y_x1, n_y_y0, n_y_y1, n_x0_x1, n_x0_y0, n_x0_y1, n_x1_y0, n_x1_y1, n_y0_y1⟩ := P.ne
  obtain ⟨hA, h0, h1, hy', hy0, hy1⟩ := hR
  have hx' : σ' x = [] := by
    cases hxv : σ' x with
    | nil => rfl
    | cons v vs => have := hT lc; rw [step_graph P.hc', fire_fork hxv] at this; cases this
  have hx0' : σ' x0 = [] := by
    cases hv : σ' x0 with
    | nil => rfl
    | cons v vs =>
      have := hT lf
      rw [step_graph P.hf', fire_comp (by intro c hc; simp at hc; subst hc; rw [hv]; simp)] at this; cases this
  have hx1' : σ' x1 = [] := by
    cases hv : σ' x1 with
    | nil => rfl
    | cons v vs =>
      have := hT le
      rw [step_graph P.he', fire_comp (by intro c hc; simp at hc; subst hc; rw [hv]; simp)] at this; cases this
  obtain ⟨n, hrun⟩ := drain_fork P.hf (by simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm]) (σ y) σ rfl
  have heq : (fun c => if c = y then [] else if c ∈ [y0, y1] then σ c ++ σ y else σ c) = σ' := by
    funext c
    by_cases a : c ∈ [y, x0, x1, y0, y1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at a
      rcases a with rfl | rfl | rfl | rfl | rfl
      · simp [hy']
      · simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, h0, hx0']
      · simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, h1, hx1']
      · simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, hy0, hx0', gm]
      · simp [n_x_y, n_x_y.symm, n_x_x0, n_x_x0.symm, n_x_x1, n_x_x1.symm, n_x_y0, n_x_y0.symm, n_x_y1, n_x_y1.symm, n_y_x0, n_y_x0.symm, n_y_x1, n_y_x1.symm, n_y_y0, n_y_y0.symm, n_y_y1, n_y_y1.symm, n_x0_x1, n_x0_x1.symm, n_x0_y0, n_x0_y0.symm, n_x0_y1, n_x0_y1.symm, n_x1_y0, n_x1_y0.symm, n_x1_y1, n_x1_y1.symm, n_y0_y1, n_y0_y1.symm, hy1, hx1', gm]
    · obtain ⟨c1, c2, c3, c4, c5⟩ := notD a
      simp [c1, c4, c5]; exact (hA c a).symm
  rw [heq] at hrun
  refine ⟨σ', n, hrun, ?_, fun _ _ => rfl⟩
  intro l
  by_cases e1 : l = lc
  · rw [e1, step_graph P.hc, fire_comp_none (List.mem_singleton_self x) hx']; rfl
  · by_cases e2 : l = lf
    · rw [e2, step_graph P.hf, fire_fork_none hy']; rfl
    · by_cases e3 : l = le
      · rw [e3]; exact none_none P.he σ'
      · have := hT l
        cases hr : rs[l]? with
        | none => exact none_none hr σ'
        | some r =>
          have hr' : rs'[l]? = some r := by rw [P.same e1 e2 e3, hr]
          rw [step_graph hr'] at this; rw [step_graph hr, this]

theorem relFC_init {σ0 : Store Nat Nat} (hy : σ0 y = []) (h0 : σ0 x0 = []) (h1 : σ0 x1 = []) :
    RelFC y x0 x1 y0 y1 G σ0 σ0 :=
  ⟨fun _ _ => rfl, h0, h1, hy, by simp [hy, h0, gm], by simp [hy, h1, gm]⟩

theorem fc_forward (P : PatFC rs rs' lc lf le x y x0 x1 y0 y1 G) {σ0 t : Store Nat Nat} {n : Nat}
    (hy : σ0 y = []) (h0 : σ0 x0 = []) (h1 : σ0 x1 = [])
    (hr : Run (step (graph rs)) σ0 n t) (ht : Terminal (step (graph rs)) t) :
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧ Agree [y, x0, x1] t t' :=
  sim_complete (RelFC y x0 x1 y0 y1 G) (Agree [y, x0, x1]) (fc_fwd_step P) (fc_fwd_term P) hr ht σ0
    (relFC_init hy h0 h1)

theorem fc_backward (P : PatFC rs rs' lc lf le x y x0 x1 y0 y1 G) {σ0 t' : Store Nat Nat} {n : Nat}
    (hy : σ0 y = []) (h0 : σ0 x0 = []) (h1 : σ0 x1 = [])
    (hr : Run (step (graph rs')) σ0 n t') (ht : Terminal (step (graph rs')) t') :
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧ Agree [y, x0, x1] t' t :=
  sim_complete (fun σ' σ => RelFC y x0 x1 y0 y1 G σ σ') (Agree [y, x0, x1])
    (fun σ' σ l u' hR hs => fc_bwd_step P σ' σ l u' hR hs) (fun σ' σ hR hT => fc_bwd_term P σ' σ hR hT)
    hr ht σ0 (relFC_init hy h0 h1)

end FC

end Formal.Rewrite.Steps
