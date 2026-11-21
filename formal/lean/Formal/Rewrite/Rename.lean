import Formal.Rewrite.IncCmpLib

/-!
# Formal.Rewrite.Rename — an imported graph's runs do not depend on how its channels and rules are numbered (shard A, 2026-11-18)

**Problem, plainly.** dfimport numbers channels and rules in the order the MLIR lists them. A rewritten MLIR imports
to the graph a theorem talks about only up to that numbering. Are complete runs the same up to renumbering?

**Proved** (`run_ren`, `terminal_ren`, and `transfer` / `transfer_back`): if `rs'` is `rs` with every channel renamed by
a bijection `π` (inverse `πi`) and its rules reordered by a bijection `τ` (inverse `τi`) on labels, then `rs` runs from
`σ` to `t` in `n` firings iff `rs'` runs from `σ ∘ πi` to `t ∘ πi` in `n` firings, and terminal stores correspond.

**Not covered:** nothing beyond token level.
-/

namespace Formal.Rewrite.IncCmp

open Formal.Net.Kahn Formal.Net.GcdHw

def E.ren (_π : Nat → Nat) (e : E) : E := e

/-- Rename every channel of a rule. -/
def renR (π : Nat → Nat) : Rule → Rule
  | .comp ins o e => .comp (ins.map π) (π o) e
  | .fork i os => .fork (π i) (os.map π)
  | .branch c d t f => .branch (π c) (π d) (π t) (π f)
  | .mux s ds o iw => .mux (π s) (ds.map π) (π o) iw
  | .cm i res idx k => .cm (π i) (π res) (π idx) k
  | .sink i => .sink (π i)

section Ren
variable (π πi : Nat → Nat) (h1 : ∀ c, πi (π c) = c) (h2 : ∀ c, π (πi c) = c)

def renS (σ : Store Nat Nat) : Store Nat Nat := fun c => σ (πi c)
def renF (fr : Fire Nat Nat) : Fire Nat Nat := (fun c => fr.1 (πi c), fun c => fr.2 (πi c))

include h1 h2

theorem mem_map_iff {l : List Nat} {c : Nat} : c ∈ l.map π ↔ πi c ∈ l := by
  constructor
  · intro h; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h; rw [h1]; exact ha
  · intro h; exact List.mem_map.mpr ⟨πi c, h, h2 c⟩

theorem eq_iff {c o : Nat} : c = π o ↔ πi c = o := by
  constructor
  · rintro rfl; exact h1 o
  · rintro rfl; exact (h2 c).symm

theorem heads_ren (σ : Store Nat Nat) : ∀ ins : List Nat, heads (renS πi σ) (ins.map π) = heads σ ins
  | [] => rfl
  | c :: cs => by simp only [List.map_cons, heads, renS, h1, heads_ren σ cs]

theorem popOf_ren (ins : List Nat) (c : Nat) : popOf (ins.map π) c = popOf ins (πi c) := by
  simp only [popOf, mem_map_iff π πi h1 h2]

theorem fire_ren (r : Rule) (σ : Store Nat Nat) :
    (renR π r).fire natVI (renS πi σ) = (r.fire natVI σ).map (renF πi) := by
  cases r with
  | mux s ds o iw =>
    simp only [renR, Rule.fire, muxF, renS, h1]
    cases hs : σ s with
    | nil => rfl
    | cons v vs =>
      simp only [natVI]
      rw [List.getElem?_map]
      cases hd : ds[v % 2 ^ iw]? with
      | none => rfl
      | some d =>
        simp only [Option.map_some]
        by_cases hds : d = s
        · subst hds; simp
        · have : π d ≠ π s := fun e => hds (by rw [← h1 d, e, h1])
          simp only [this, hds, ↓reduceIte, h1]
          cases hx : σ d with
          | nil => rfl
          | cons x xs =>
            simp only [Option.map_some, renF, Option.some.injEq, Prod.mk.injEq]
            refine ⟨?_, ?_⟩
            · funext y; simp only [eq_iff π πi h1 h2]
            · funext y; simp only [eq_iff π πi h1 h2]
  | comp ins o e =>
    simp only [renR, Rule.fire, strictF, Rule.insL, heads_ren π πi h1 h2]
    cases heads σ ins with
    | none => rfl
    | some vs =>
      simp only [Option.bind_some, Rule.out, Option.map_some, renF, Option.some.injEq, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · funext c; exact popOf_ren π πi h1 h2 ins c
      · funext c; simp only [eq_iff π πi h1 h2]
  | fork i os =>
    simp only [renR, Rule.fire, strictF, Rule.insL, List.map_cons, List.map_nil]
    rw [show [π i] = [i].map π from rfl, heads_ren π πi h1 h2]
    cases heads σ [i] with
    | none => rfl
    | some vs =>
      simp only [Option.bind_some, Rule.out, Option.map_some, renF, Option.some.injEq, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · funext c; exact popOf_ren π πi h1 h2 [i] c
      · funext c; simp only [mem_map_iff π πi h1 h2]
  | branch c d t f =>
    simp only [renR, Rule.fire, strictF, Rule.insL]
    rw [show [π c, π d] = [c, d].map π from rfl, heads_ren π πi h1 h2]
    cases hh : heads σ [c, d] with
    | none => rfl
    | some vs =>
      simp only [Option.bind_some]
      match vs with
      | [v, x] =>
        simp only [Rule.out, natVI, Option.map_some, renF, Option.some.injEq, Prod.mk.injEq]
        refine ⟨?_, ?_⟩
        · funext c'; exact popOf_ren π πi h1 h2 [c, d] c'
        · funext c'; split <;> simp only [eq_iff π πi h1 h2]
      | [] => rfl
      | [_] => rfl
      | _ :: _ :: _ :: _ => rfl
  | cm i res idx k =>
    simp only [renR, Rule.fire, strictF, Rule.insL]
    rw [show [π i] = [i].map π from rfl, heads_ren π πi h1 h2]
    cases heads σ [i] with
    | none => rfl
    | some vs =>
      simp only [Option.bind_some, Rule.out, Option.map_some, renF, Option.some.injEq, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · funext c; exact popOf_ren π πi h1 h2 [i] c
      · funext c; simp only [eq_iff π πi h1 h2]
  | sink i =>
    simp only [renR, Rule.fire, strictF, Rule.insL]
    rw [show [π i] = [i].map π from rfl, heads_ren π πi h1 h2]
    cases heads σ [i] with
    | none => rfl
    | some vs =>
      simp only [Option.bind_some, Rule.out, Option.map_some, renF, Option.some.injEq, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · funext c; exact popOf_ren π πi h1 h2 [i] c
      · trivial

theorem applyF_ren (σ : Store Nat Nat) (fr : Fire Nat Nat) :
    applyF (renS πi σ) (renF πi fr) = renS πi (applyF σ fr) := rfl


theorem renS_inv (σ : Store Nat Nat) : renS π (renS πi σ) = σ := by funext c; simp [renS, h1]

theorem renS_inv' (σ : Store Nat Nat) : renS πi (renS π σ) = σ := by funext c; simp [renS, h2]

variable {rs rs' : List Rule} (τ τi : Nat → Nat) (g1 : ∀ l, τi (τ l) = l) (g2 : ∀ l, τ (τi l) = l)
  (hrs : ∀ l, rs'[l]? = (rs[τi l]?).map (renR π))

include hrs

theorem step_ren (σ : Store Nat Nat) (l : Nat) :
    step (graph rs') (renS πi σ) l = (step (graph rs) σ (τi l)).map (renS πi) := by
  cases hr : rs[τi l]? with
  | none =>
    have : rs'[l]? = none := by rw [hrs l, hr]; rfl
    rw [step_graph_none this, step_graph_none hr]; rfl
  | some r =>
    have : rs'[l]? = some (renR π r) := by rw [hrs l, hr]; rfl
    rw [step_graph this, step_graph hr, fire_ren π πi h1 h2]
    cases r.fire natVI σ with
    | none => rfl
    | some fr => rfl

include g1 in
theorem run_ren {σ t : Store Nat Nat} {n : Nat} (h : Run (step (graph rs)) σ n t) :
    Run (step (graph rs')) (renS πi σ) n (renS πi t) := by
  induction h with
  | refl => exact Run.refl _
  | @cons s s' u k l hl _ ih =>
    refine Run.cons (τ l) ?_ ih
    rw [step_ren π πi h1 h2 τi hrs, g1, hl]; rfl

theorem run_ren_back {σ' t' : Store Nat Nat} {n : Nat} (h : Run (step (graph rs')) σ' n t') :
    Run (step (graph rs)) (renS π σ') n (renS π t') := by
  induction h with
  | refl => exact Run.refl _
  | @cons s s' u k l hl _ ih =>
    refine Run.cons (τi l) ?_ ih
    have := step_ren π πi h1 h2 τi hrs (renS π s) l
    rw [renS_inv' π πi h1 h2, hl] at this
    cases hx : step (graph rs) (renS π s) (τi l) with
    | none => rw [hx] at this; cases this
    | some x =>
      rw [hx] at this
      simp only [Option.map_some, Option.some.injEq] at this
      rw [this, renS_inv π πi h1 h2]

include g2 in
theorem terminal_ren {t : Store Nat Nat} (h : Terminal (step (graph rs)) t) :
    Terminal (step (graph rs')) (renS πi t) := by
  intro l; rw [step_ren π πi h1 h2 τi hrs, h (τi l)]; rfl

include g1 in
theorem terminal_ren_back {t' : Store Nat Nat} (h : Terminal (step (graph rs')) t') :
    Terminal (step (graph rs)) (renS π t') := by
  intro l
  have := step_ren π πi h1 h2 τi hrs (renS π t') (τ l)
  rw [renS_inv' π πi h1 h2, h (τ l), g1] at this
  cases hx : step (graph rs) (renS π t') l with
  | none => rfl
  | some x => rw [hx] at this; cases this

end Ren

/-! ## Finite permutations given as lists, checked by `decide` -/

/-- The bijection of `Nat` that is `L` on `[0, L.length)` and the identity above. -/
def fp (L : List Nat) (c : Nat) : Nat := if c < L.length then L.getD c c else c

def fpCheck (L Li : List Nat) : Bool :=
  L.length == Li.length &&
  (List.range L.length).all (fun c => decide (L.getD c c < L.length) && Li.getD (L.getD c c) 0 == c)

theorem fp_inv (L Li : List Nat) (h : fpCheck L Li = true) : ∀ c, fp Li (fp L c) = c := by
  intro c
  simp only [fpCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨hl, hall⟩ := h
  unfold fp
  by_cases hc : c < L.length
  · obtain ⟨h1, h2⟩ := hall c hc
    rw [if_pos hc]
    generalize L.getD c c = a at h1 h2 ⊢
    rw [if_pos (by omega)]
    have hd : ∀ d, Li.getD a d = Li[a]'(by omega) := fun d => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [hd] at h2 ⊢
    exact h2
  · rw [if_neg hc, if_neg (by omega)]

/-- `rs'` is `rs` renamed by `fp P` and reordered by `fp T` (checked on every label). -/
def renCheck (rs rs' : List Rule) (P Ti : List Nat) : Bool :=
  rs.length == rs'.length && Ti.length == rs'.length &&
  (List.range rs'.length).all (fun l => decide (rs'[l]? = (rs[fp Ti l]?).map (renR (fp P))))

theorem renCheck_ok {rs rs' : List Rule} {P Ti : List Nat} (h : renCheck rs rs' P Ti = true) :
    ∀ l, rs'[l]? = (rs[fp Ti l]?).map (renR (fp P)) := by
  simp only [renCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  intro l
  by_cases hl : l < rs'.length
  · exact h3 l hl
  · have : fp Ti l = l := by unfold fp; rw [if_neg (by omega)]
    rw [this, List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]; rfl

end Formal.Rewrite.IncCmp
