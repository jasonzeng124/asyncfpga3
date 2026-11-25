import Formal.Net.GcdHwLib

/-!
# Formal.Rewrite.IncCmpLib — helpers for graph-level rewrite proofs (shard A, 2026-11-18)

Core Lean only. Three things used by `Formal.Rewrite.IncCmpGraph`:
* `sim_complete`: a weak simulation between two transition systems that also maps terminal states to
  terminal states carries every complete run of the first to a complete run of the second.
* the firing of a single-input `comp` rule and of a two-output `fork` rule in an imported graph
  (`step_comp1`, `step_fork2`), and their "drain" runs (fire until the input channel is empty).
* `fire_congr`: a rule's firing depends only on its input channels.
-/

namespace Formal.Rewrite.IncCmp

open Formal.Net.Kahn Formal.Net.GcdHw

/-! ## Abstract simulation -/

section Abs
variable {S T L M : Type} {stA : S → L → Option S} {stB : T → M → Option T}

theorem sim_complete (R : S → T → Prop) (Obs : S → T → Prop)
    (hstep : ∀ s t l s1, R s t → stA s l = some s1 → ∃ t1 n, Run stB t n t1 ∧ R s1 t1)
    (hterm : ∀ s t, R s t → Terminal stA s → ∃ t1 n, Run stB t n t1 ∧ Terminal stB t1 ∧ Obs s t1) :
    ∀ {s n u}, Run stA s n u → Terminal stA u → ∀ t, R s t →
      ∃ t1 m, Run stB t m t1 ∧ Terminal stB t1 ∧ Obs u t1 := by
  intro s n u hr hu
  induction hr with
  | refl s => intro t hR; exact hterm s t hR hu
  | @cons s s' u' k l hl _ ih =>
    intro t hR
    obtain ⟨t1, n1, hr1, hR1⟩ := hstep s t l s' hR hl
    obtain ⟨t2, m2, hr2, ht2, hO⟩ := ih hu t1 hR1
    exact ⟨t2, n1 + m2, run_trans hr1 hr2, ht2, hO⟩

end Abs

/-! ## Point updates of a store -/

/-- `upd σ ch l`: the store `σ` with channel `ch` set to `l`. -/
def upd {V : Type} (σ : Store Nat V) (ch : Nat) (l : List V) : Store Nat V :=
  fun c => if c = ch then l else σ c

@[simp] theorem upd_same {V : Type} (σ : Store Nat V) (ch : Nat) (l : List V) : upd σ ch l ch = l := by
  simp [upd]

@[simp] theorem upd_other {V : Type} (σ : Store Nat V) {ch c : Nat} (l : List V) (h : c ≠ ch) :
    upd σ ch l c = σ c := by simp [upd, h]

/-! ## Firing single rules -/

theorem step_graph {rs : List Rule} {l : Nat} {r : Rule} (hr : rs[l]? = some r) (σ : Store Nat Nat) :
    step (graph rs) σ l = (r.fire natVI σ).map (applyF σ) := by
  simp only [step, graph, graphV, hr]; rfl

theorem step_graph_none {rs : List Rule} {l : Nat} (hr : rs[l]? = none) (σ : Store Nat Nat) :
    step (graph rs) σ l = none := by
  simp only [step, graph, graphV, hr]; rfl

/-- A single-input `comp` with a token fires: pop it, push `f(v)`. -/
theorem step_comp1 {rs : List Rule} {l i o : Nat} {f : E} (hr : rs[l]? = some (.comp [i] o f))
    (hio : i ≠ o) {σ : Store Nat Nat} {v : Nat} {vs : List Nat} (hσ : σ i = v :: vs) :
    step (graph rs) σ l = some (upd (upd σ i vs) o (σ o ++ [f.eval [v]])) := by
  rw [step_graph hr]
  simp only [Rule.fire, strictF, heads, hσ, Rule.out, natVI, Rule.insL]
  simp only [Option.map_some, Option.bind_some, Option.some.injEq]
  funext c
  simp only [applyF, popOf, upd, List.mem_singleton]
  by_cases h1 : c = o
  · subst h1; simp [Ne.symm hio]
  · by_cases h2 : c = i
    · subst h2; simp [hσ, h1]
    · simp [h1, h2]

theorem step_comp1_none {rs : List Rule} {l i o : Nat} {f : E} (hr : rs[l]? = some (.comp [i] o f))
    {σ : Store Nat Nat} (hσ : σ i = []) : step (graph rs) σ l = none := by
  rw [step_graph hr]
  simp only [Rule.fire, strictF, heads, hσ, Rule.insL]; rfl

/-- A two-output `fork` with a token fires: pop it, push it on both outputs. -/
theorem step_fork2 {rs : List Rule} {l i o1 o2 : Nat} (hr : rs[l]? = some (.fork i [o1, o2]))
    (h1 : i ≠ o1) (h2 : i ≠ o2) (h12 : o1 ≠ o2) {σ : Store Nat Nat} {v : Nat} {vs : List Nat}
    (hσ : σ i = v :: vs) :
    step (graph rs) σ l = some (upd (upd (upd σ i vs) o1 (σ o1 ++ [v])) o2 (σ o2 ++ [v])) := by
  rw [step_graph hr]
  simp only [Rule.fire, strictF, heads, hσ, Rule.out, Rule.insL]
  simp only [Option.map_some, Option.bind_some, Option.some.injEq]
  funext c
  simp only [applyF, popOf, upd, List.mem_cons, List.not_mem_nil, or_false]
  by_cases e2 : c = o2
  · subst e2; simp [Ne.symm h2, Ne.symm h12]
  · by_cases e1 : c = o1
    · subst e1; simp [Ne.symm h1, e2]
    · by_cases e0 : c = i
      · subst e0; simp [hσ, e1, e2]
      · simp [e0, e1, e2]

theorem step_fork2_none {rs : List Rule} {l i o1 o2 : Nat} (hr : rs[l]? = some (.fork i [o1, o2]))
    {σ : Store Nat Nat} (hσ : σ i = []) : step (graph rs) σ l = none := by
  rw [step_graph hr]
  simp only [Rule.fire, strictF, heads, hσ, Rule.insL]; rfl

/-! ## Drain runs -/

/-- Fire a single-input `comp` until its input is empty. -/
theorem drain_comp1 {rs : List Rule} {l i o : Nat} {f : E} (hr : rs[l]? = some (.comp [i] o f))
    (hio : i ≠ o) : ∀ (xs : List Nat) (σ : Store Nat Nat), σ i = xs →
    ∃ n, Run (step (graph rs)) σ n (upd (upd σ i []) o (σ o ++ xs.map (fun v => f.eval [v]))) := by
  intro xs
  induction xs with
  | nil =>
    intro σ hσ
    refine ⟨0, run_refl_eq ?_⟩
    funext c; simp only [upd, List.map_nil, List.append_nil]
    by_cases h1 : c = o
    · subst h1; simp
    · by_cases h2 : c = i
      · subst h2; simp [hσ, h1]
      · simp [h1, h2]
  | cons v vs ih =>
    intro σ hσ
    have hs := step_comp1 hr hio hσ
    obtain ⟨n, hrun⟩ := ih (upd (upd σ i vs) o (σ o ++ [f.eval [v]])) (by simp [upd, hio])
    refine ⟨n + 1, Run.cons l hs ?_⟩
    have e : upd (upd (upd (upd σ i vs) o (σ o ++ [f.eval [v]])) i []) o
        ((upd (upd σ i vs) o (σ o ++ [f.eval [v]])) o ++ vs.map (fun v => f.eval [v])) =
        upd (upd σ i []) o (σ o ++ (v :: vs).map (fun v => f.eval [v])) := by
      funext c; simp only [upd]
      by_cases h1 : c = o
      · subst h1; simp
      · by_cases h2 : c = i
        · subst h2; simp [h1]
        · simp [h1, h2]
    rw [e] at hrun; exact hrun

/-- Fire a two-output `fork` until its input is empty. -/
theorem drain_fork2 {rs : List Rule} {l i o1 o2 : Nat} (hr : rs[l]? = some (.fork i [o1, o2]))
    (h1 : i ≠ o1) (h2 : i ≠ o2) (h12 : o1 ≠ o2) : ∀ (xs : List Nat) (σ : Store Nat Nat), σ i = xs →
    ∃ n, Run (step (graph rs)) σ n (upd (upd (upd σ i []) o1 (σ o1 ++ xs)) o2 (σ o2 ++ xs)) := by
  intro xs
  induction xs with
  | nil =>
    intro σ hσ
    refine ⟨0, run_refl_eq ?_⟩
    funext c; simp only [upd, List.append_nil]
    by_cases e2 : c = o2
    · subst e2; simp
    · by_cases e1 : c = o1
      · subst e1; simp [e2]
      · by_cases e0 : c = i
        · subst e0; simp [hσ, e1, e2]
        · simp [e0, e1, e2]
  | cons v vs ih =>
    intro σ hσ
    have hs := step_fork2 hr h1 h2 h12 hσ
    obtain ⟨n, hrun⟩ := ih (upd (upd (upd σ i vs) o1 (σ o1 ++ [v])) o2 (σ o2 ++ [v]))
      (by simp [upd, h1, h2])
    refine ⟨n + 1, Run.cons l hs ?_⟩
    have e : upd (upd (upd (upd (upd (upd σ i vs) o1 (σ o1 ++ [v])) o2 (σ o2 ++ [v])) i []) o1
        ((upd (upd (upd σ i vs) o1 (σ o1 ++ [v])) o2 (σ o2 ++ [v])) o1 ++ vs)) o2
        ((upd (upd (upd σ i vs) o1 (σ o1 ++ [v])) o2 (σ o2 ++ [v])) o2 ++ vs) =
        upd (upd (upd σ i []) o1 (σ o1 ++ v :: vs)) o2 (σ o2 ++ v :: vs) := by
      funext c; simp only [upd]
      by_cases e2 : c = o2
      · subst e2; simp
      · by_cases e1 : c = o1
        · subst e1; simp [e2]
        · by_cases e0 : c = i
          · subst e0; simp [e1, e2]
          · simp [e0, e1, e2]
    rw [e] at hrun; exact hrun

/-! ## A firing depends only on the input channels -/

theorem heads_congr {σ τ : Store Nat Nat} : ∀ {cs : List Nat}, (∀ c ∈ cs, σ c = τ c) → heads σ cs = heads τ cs
  | [], _ => rfl
  | c :: cs, h => by
    simp only [heads]
    rw [h c (by simp), heads_congr (fun d hd => h d (by simp [hd]))]

theorem fire_congr (r : Rule) {σ τ : Store Nat Nat} (h : ∀ c ∈ r.insL, σ c = τ c) :
    r.fire natVI σ = r.fire natVI τ := by
  cases r with
  | mux s ds o iw =>
    simp only [Rule.fire, muxF]
    have hs : σ s = τ s := h s (by simp [Rule.insL])
    rw [hs]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · rename_i d hd
          have hd' : σ d = τ d := h d (by simp only [Rule.insL, List.mem_cons]; exact Or.inr (List.mem_of_getElem? hd))
          rw [hd']
  | _ => simp only [Rule.fire, strictF]; rw [heads_congr h]

end Formal.Rewrite.IncCmp
