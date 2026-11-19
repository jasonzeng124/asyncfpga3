import Formal.Rewrite.IncCmpLib

/-!
# Formal.Rewrite.Steps.Basic — shared lemmas for the local rewrite steps (shard A, 2026-11-19)

Core Lean only. What every local rewrite step (`Absorb`, `ForkJoin`, `ForkSplit`, `ForkComm`, `Cong`) needs:
* the firing of a strict `comp` rule with any number of distinct inputs, and of a `fork` with distinct outputs,
  stated pointwise (`applyF`), so no proof has to chain `upd`s;
* the frame lemma: a rule that reads none of the channels on which two stores differ fires the same way in both, and
  its firing changes a differing channel only by appending (`outside_step`);
* `Agree D σ σ'`: the stores are equal outside the list `D`.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

/-- Two stores agree outside the channel list `D`. -/
def Agree (D : List Nat) (σ σ' : Store Nat Nat) : Prop := ∀ c, c ∉ D → σ' c = σ c

theorem Agree.symm {D : List Nat} {σ σ' : Store Nat Nat} (h : Agree D σ σ') : Agree D σ' σ :=
  fun c hc => (h c hc).symm

theorem Agree.mono {D D' : List Nat} {σ σ' : Store Nat Nat} (h : Agree D σ σ') (hs : ∀ c ∈ D, c ∈ D') :
    Agree D' σ σ' := fun c hc => h c (fun h' => hc (hs c h'))

theorem Agree.trans {D D' : List Nat} {σ σ' σ'' : Store Nat Nat} (h : Agree D σ σ') (h' : Agree D' σ' σ'') :
    Agree (D ++ D') σ σ'' := fun c hc => by
  simp only [List.mem_append, not_or] at hc
  rw [h' c hc.2, h c hc.1]

/-- The front of a channel (0 if empty; only used where the channel is non-empty). -/
def hd (σ : Store Nat Nat) (c : Nat) : Nat := (σ c).headD 0

theorem heads_all {σ : Store Nat Nat} : ∀ {ins : List Nat}, (∀ c ∈ ins, σ c ≠ []) →
    heads σ ins = some (ins.map (hd σ))
  | [], _ => rfl
  | c :: cs, h => by
    have h0 := h c (by simp)
    have ih := heads_all (ins := cs) (fun d hd' => h d (by simp [hd']))
    simp only [heads, List.map_cons]
    cases hc : σ c with
    | nil => exact absurd hc h0
    | cons v vs => simp [ih, hd, hc]

theorem heads_none {σ : Store Nat Nat} : ∀ {ins : List Nat} {c : Nat}, c ∈ ins → σ c = [] → heads σ ins = none
  | [], _, hc, _ => by cases hc
  | d :: ds, c, hc, he => by
    simp only [heads]
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [he]
    · split
      · rfl
      · rw [heads_none hc he]; rfl

theorem heads_some_iff {σ : Store Nat Nat} {ins : List Nat} {vs : List Nat} (h : heads σ ins = some vs) :
    (∀ c ∈ ins, σ c ≠ []) ∧ vs = ins.map (hd σ) := by
  have hn := heads_nonempty h
  refine ⟨hn, ?_⟩
  rw [heads_all hn] at h; exact (Option.some.inj h).symm

/-! ## Firing a comp and a fork -/

theorem fire_comp {ins : List Nat} {o : Nat} {F : E} {σ : Store Nat Nat} (h : ∀ c ∈ ins, σ c ≠ []) :
    (Rule.comp ins o F).fire natVI σ =
      some (popOf ins, fun c => if c = o then [F.eval (ins.map (hd σ))] else []) := by
  simp only [Rule.fire, strictF, heads_all h, Rule.insL, Option.bind_some, Rule.out, natVI, Option.map_some]

theorem fire_comp_none {ins : List Nat} {o : Nat} {F : E} {σ : Store Nat Nat} {c : Nat} (hc : c ∈ ins)
    (he : σ c = []) : (Rule.comp ins o F).fire natVI σ = none := by
  simp only [Rule.fire, strictF, Rule.insL, heads_none hc he, Option.bind_none]

theorem fire_fork {i : Nat} {os : List Nat} {σ : Store Nat Nat} {v : Nat} {vs : List Nat} (h : σ i = v :: vs) :
    (Rule.fork i os).fire natVI σ = some (popOf [i], fun c => if c ∈ os then [v] else []) := by
  simp only [Rule.fire, strictF, Rule.insL, heads, h, Option.map_some, Option.bind_some, Rule.out]
  rfl

theorem fire_fork_none {i : Nat} {os : List Nat} {σ : Store Nat Nat} (h : σ i = []) :
    (Rule.fork i os).fire natVI σ = none := by
  simp only [Rule.fire, strictF, Rule.insL, heads, h, Option.bind_none]

theorem fire_sink_none {i : Nat} {σ : Store Nat Nat} (h : σ i = []) : (Rule.sink i).fire natVI σ = none := by
  simp only [Rule.fire, strictF, Rule.insL, heads, h, Option.bind_none]

theorem applyF_at (σ : Store Nat Nat) (fr : Fire Nat Nat) (c : Nat) : applyF σ fr c = (σ c).drop (fr.1 c) ++ fr.2 c :=
  rfl

theorem popOf_mem {ins : List Nat} {c : Nat} (h : c ∈ ins) : popOf ins c = 1 := by simp [popOf, h]
theorem popOf_nmem {ins : List Nat} {c : Nat} (h : c ∉ ins) : popOf ins c = 0 := by simp [popOf, h]

/-- After a comp fires: an input loses its front, the output gains `F(heads)`, everything else is unchanged
(inputs distinct from the output). -/
theorem comp_at {ins : List Nat} {o : Nat} {F : E} {σ : Store Nat Nat} (ho : o ∉ ins) (c : Nat) :
    applyF σ (popOf ins, fun c => if c = o then [F.eval (ins.map (hd σ))] else []) c =
      if c ∈ ins then (σ c).tail else if c = o then σ c ++ [F.eval (ins.map (hd σ))] else σ c := by
  simp only [applyF_at, popOf]
  by_cases h1 : c ∈ ins
  · have : c ≠ o := fun e => ho (e ▸ h1)
    simp [h1, this, List.drop_one]
  · by_cases h2 : c = o
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem fork_at {i : Nat} {os : List Nat} {σ : Store Nat Nat} {v : Nat} (hi : i ∉ os) (c : Nat) :
    applyF σ (popOf [i], fun c => if c ∈ os then [v] else []) c =
      if c = i then (σ c).tail else if c ∈ os then σ c ++ [v] else σ c := by
  simp only [applyF_at, popOf, List.mem_singleton]
  by_cases h1 : c = i
  · subst h1; simp [hi, List.drop_one]
  · by_cases h2 : c ∈ os <;> simp [h1, h2]

/-! ## The frame lemma -/

/-- A rule that reads no channel of `D` fires the same way on two stores that agree outside `D`. -/
theorem fire_agree {D : List Nat} {σ σ' : Store Nat Nat} (hA : Agree D σ σ') (r : Rule)
    (hr : ∀ c ∈ r.insL, c ∉ D) : r.fire natVI σ' = r.fire natVI σ :=
  fire_congr r (fun c hc => hA c (hr c hc))

theorem nin_of {r : Rule} {D : List Nat} (hrd : ∀ c ∈ r.insL, c ∉ D) {c : Nat} (h : c ∈ D) : c ∉ r.insL :=
  fun h' => hrd c h' h

/-- A firing pops only from the rule's inputs and pushes only on its outputs. -/
theorem fire_pop0 {r : Rule} {σ : Store Nat Nat} {fr : Fire Nat Nat} (h : r.fire natVI σ = some fr) {c : Nat}
    (hc : c ∉ r.insL) : fr.1 c = 0 := (r.node natVI).pop_ins σ fr c h hc

theorem fire_push0 {r : Rule} {σ : Store Nat Nat} {fr : Fire Nat Nat} (h : r.fire natVI σ = some fr) {c : Nat}
    (hc : c ∉ r.outsL) : fr.2 c = [] := (r.node natVI).push_outs σ fr c h hc

/-- The same firing applied to two stores that agree outside `D` gives stores that agree outside `D`. -/
theorem applyF_agree {D : List Nat} {σ σ' : Store Nat Nat} (hA : Agree D σ σ') (fr : Fire Nat Nat) :
    Agree D (applyF σ fr) (applyF σ' fr) := fun c hc => by simp only [applyF_at, hA c hc]

/-- On a channel the rule does not read, its firing only appends. -/
theorem applyF_app {r : Rule} {σ : Store Nat Nat} {fr : Fire Nat Nat} (h : r.fire natVI σ = some fr) {c : Nat}
    (hc : c ∉ r.insL) : applyF σ fr c = σ c ++ fr.2 c := by
  simp [applyF_at, fire_pop0 h hc]

/-- The outside step: a label that holds the same rule in both graphs, reading nothing in `D`. -/
theorem outside_step {rs rs' : List Rule} {D : List Nat} {l : Nat} {r : Rule} (hl : rs[l]? = some r)
    (hl' : rs'[l]? = some r) (hr : ∀ c ∈ r.insL, c ∉ D) {σ σ' u : Store Nat Nat} (hA : Agree D σ σ')
    (hs : step (graph rs) σ l = some u) :
    ∃ fr, r.fire natVI σ = some fr ∧ u = applyF σ fr ∧ step (graph rs') σ' l = some (applyF σ' fr) := by
  rw [step_graph hl] at hs
  cases hf : r.fire natVI σ with
  | none => rw [hf] at hs; cases hs
  | some fr =>
    rw [hf] at hs
    refine ⟨fr, rfl, (Option.some.inj hs).symm, ?_⟩
    rw [step_graph hl', fire_agree hA r hr, hf]; rfl

theorem outside_none {rs rs' : List Rule} {D : List Nat} {l : Nat} {r : Rule} (hl : rs[l]? = some r)
    (hl' : rs'[l]? = some r) (hr : ∀ c ∈ r.insL, c ∉ D) {σ σ' : Store Nat Nat} (hA : Agree D σ σ')
    (hs : step (graph rs) σ l = none) : step (graph rs') σ' l = none := by
  rw [step_graph hl] at hs; rw [step_graph hl', fire_agree hA r hr]
  cases hf : r.fire natVI σ with
  | none => rfl
  | some fr => rw [hf] at hs; cases hs


/-- The outside step, when the second store extends the first on the rule's inputs (`σ c = σ' c ++ z`): a firing
on `σ'` is the same firing on `σ` (monotonicity of strict rules). -/
theorem outside_step_ext {rs rs' : List Rule} {l : Nat} {r : Rule} (hl : rs[l]? = some r)
    (hl' : rs'[l]? = some r) {σ σ' u' : Store Nat Nat} (hx : ∀ c ∈ r.insL, ∃ z, σ c = σ' c ++ z)
    (hs : step (graph rs') σ' l = some u') :
    ∃ fr, r.fire natVI σ' = some fr ∧ r.fire natVI σ = some fr ∧ u' = applyF σ' fr ∧
      step (graph rs) σ l = some (applyF σ fr) := by
  rw [step_graph hl'] at hs
  cases hf : r.fire natVI σ' with
  | none => rw [hf] at hs; cases hs
  | some fr =>
    rw [hf] at hs
    have hf2 : r.fire natVI σ = some fr := (r.node natVI).mono σ' σ fr hf hx
    refine ⟨fr, rfl, hf2, (Option.some.inj hs).symm, ?_⟩
    rw [step_graph hl, hf2]; rfl

/-- Popping at most what the shorter list holds commutes with appending. -/
theorem drop_app_of_le {A B : List Nat} {k : Nat} (h : k ≤ A.length) : (A ++ B).drop k = A.drop k ++ B :=
  List.drop_append_of_le_length h

/-- Firing a fork until its input is empty. -/
theorem drain_fork {rs : List Rule} {l i : Nat} {os : List Nat} (hr : rs[l]? = some (.fork i os)) (hi : i ∉ os) :
    ∀ (L : List Nat) (σ : Store Nat Nat), σ i = L →
      ∃ n, Run (step (graph rs)) σ n (fun c => if c = i then [] else if c ∈ os then σ c ++ L else σ c) := by
  intro L
  induction L with
  | nil =>
    intro σ hσ
    refine ⟨0, run_refl_eq ?_⟩
    funext c
    by_cases h1 : c = i
    · subst h1; simp [hσ]
    · by_cases h2 : c ∈ os <;> simp [h1, h2]
  | cons v vs ih =>
    intro σ hσ
    have hs : step (graph rs) σ l = some (applyF σ (popOf [i], fun c => if c ∈ os then [v] else [])) := by
      rw [step_graph hr, fire_fork hσ]; rfl
    obtain ⟨n, hrun⟩ := ih (applyF σ (popOf [i], fun c => if c ∈ os then [v] else []))
      (by rw [fork_at hi]; simp [hσ])
    refine ⟨n + 1, Run.cons l hs ?_⟩
    have e : (fun c => if c = i then [] else if c ∈ os then
        applyF σ (popOf [i], fun c => if c ∈ os then [v] else []) c ++ vs else
        applyF σ (popOf [i], fun c => if c ∈ os then [v] else []) c) =
        (fun c => if c = i then [] else if c ∈ os then σ c ++ v :: vs else σ c) := by
      funext c
      rw [fork_at hi]
      by_cases h1 : c = i
      · simp [h1]
      · by_cases h2 : c ∈ os <;> simp [h1, h2]
    rw [e] at hrun; exact hrun

/-- A label beyond both lists is disabled in both. -/
theorem none_none {rs : List Rule} {l : Nat} (h : rs[l]? = none) (σ : Store Nat Nat) : step (graph rs) σ l = none :=
  step_graph_none h σ

/-- A run of one label's drain, as a reusable shape: firing `l` `k` times. -/
theorem run_append {rs : List Rule} {a b c : Store Nat Nat} {m n : Nat} (h1 : Run (step (graph rs)) a m b)
    (h2 : Run (step (graph rs)) b n c) : Run (step (graph rs)) a (m + n) c := run_trans h1 h2

end Formal.Rewrite.Steps
