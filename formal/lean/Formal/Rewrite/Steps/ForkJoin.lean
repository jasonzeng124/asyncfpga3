import Formal.Rewrite.Steps.Basic

/-!
# Formal.Rewrite.Steps.ForkJoin — a fork whose outputs all feed one comp is that comp on the fork's input (shard A, 2026-11-19)

**Problem, plainly.** A fork copies `x` onto `c0, c1, ..., ck`, and one comp reads exactly those channels and
computes `y = g(c0, ..., ck)`. Is that the same, whatever surrounds it, as one comp `y = g(x, x, ..., x)` reading
`x`?

**Proved** (`fj_forward`, `fj_backward`): for ANY imported graph `rs` holding `fork x (c0 :: cr)` at `lf` and
`comp (c0 :: cr) y g` at `lc`, and `rs'` equal except `comp [x] y (g with every input replaced by x)` at `lf` and
the dead rule `sink c0` at `lc`, with `x, c0, cr` distinct, `y` not among them, no other rule reading `x` or the
`ci`, and no other rule writing the `ci`: from any store with the `ci` empty, every complete run of either graph is
matched by a complete run of the other ending in the same store outside the `ci`.

**Not covered:** token level only.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

/-- `g` with every input replaced by input 0. -/
def allZero (cs : List Nat) (g : E) : E := g.subst (cs.map fun _ => .var 0)

theorem eval_allZero (cs : List Nat) (g : E) (v : Nat) :
    (allZero cs g).eval [v] = g.eval (cs.map fun _ => v) := by
  simp only [allZero, eval_subst, List.map_map]
  congr 1

structure PatFJ (rs rs' : List Rule) (lf lc x y c0 : Nat) (cr : List Nat) (g : E) : Prop where
  hf : rs[lf]? = some (.fork x (c0 :: cr))
  hc : rs[lc]? = some (.comp (c0 :: cr) y g)
  hf' : rs'[lf]? = some (.comp [x] y (allZero (c0 :: cr) g))
  hc' : rs'[lc]? = some (.sink c0)
  hlfc : lf ≠ lc
  hsame : ∀ l, l ≠ lf → l ≠ lc → rs'[l]? = rs[l]?
  hins : ∀ l r, l ≠ lf → l ≠ lc → rs[l]? = some r → ∀ c ∈ r.insL, c ∉ x :: c0 :: cr
  houts : ∀ l r, l ≠ lf → rs[l]? = some r → ∀ c ∈ r.outsL, c ∉ c0 :: cr
  hnd : (x :: c0 :: cr).Nodup
  hy : y ∉ x :: c0 :: cr

section FJ
variable {rs rs' : List Rule} {lf lc x y c0 : Nat} {cr : List Nat} {g : E}

/-- `σ` runs `rs` (fork + comp), `σ'` runs `rs'` (one comp); `L` is what the fork has copied and the comp not yet
consumed. -/
def RelFJ (x c0 : Nat) (cr : List Nat) (σ σ' : Store Nat Nat) : Prop :=
  ∃ L : List Nat, Agree (x :: c0 :: cr) σ σ' ∧ σ' x = L ++ σ x ∧ (∀ c ∈ c0 :: cr, σ c = L) ∧
    (∀ c ∈ c0 :: cr, σ' c = [])

theorem PatFJ.x_nin (P : PatFJ rs rs' lf lc x y c0 cr g) : x ∉ c0 :: cr := (List.nodup_cons.mp P.hnd).1
theorem PatFJ.y_ne_x (P : PatFJ rs rs' lf lc x y c0 cr g) : y ≠ x := fun e => P.hy (by simp [e])
theorem PatFJ.y_nin (P : PatFJ rs rs' lf lc x y c0 cr g) : y ∉ c0 :: cr := fun h => P.hy (List.mem_cons_of_mem _ h)

/-- Outside rules: same rule in both graphs, reading nothing private. -/
theorem PatFJ.out (P : PatFJ rs rs' lf lc x y c0 cr g) {l : Nat} {r : Rule} (h1 : l ≠ lf) (h2 : l ≠ lc)
    (hr : rs[l]? = some r) : rs'[l]? = some r ∧ ∀ c ∈ r.insL, c ∉ x :: c0 :: cr :=
  ⟨by rw [P.hsame l h1 h2, hr], P.hins l r h1 h2 hr⟩

theorem fj_fwd_step (P : PatFJ rs rs' lf lc x y c0 cr g) :
    ∀ σ σ' l u, RelFJ x c0 cr σ σ' → step (graph rs) σ l = some u →
      ∃ u' n, Run (step (graph rs')) σ' n u' ∧ RelFJ x c0 cr u u' := by
  intro σ σ' l u ⟨L, hA, hx, hcs, hcs'⟩ hs
  by_cases e1 : l = lf
  · subst e1
    rw [step_graph P.hf] at hs
    cases hxv : σ x with
    | nil => rw [fire_fork_none hxv] at hs; cases hs
    | cons v vs =>
      rw [fire_fork hxv] at hs
      have hu := (Option.some.inj hs).symm
      refine ⟨σ', 0, Run.refl _, L ++ [v], ?_, ?_, ?_, ?_⟩
      · intro c hc
        rw [hu, fork_at P.x_nin]
        have h1 : c ≠ x := fun e => hc (by simp [e])
        have h2 : c ∉ c0 :: cr := fun h => hc (List.mem_cons_of_mem _ h)
        simp [h1, h2, hA c hc]
      · rw [hu, fork_at P.x_nin, hx, hxv]; simp
      · intro c hc
        rw [hu, fork_at P.x_nin]
        have h1 : c ≠ x := fun e => P.x_nin (e ▸ hc)
        simp [h1, hc, hcs c hc]
      · exact hcs'
  · by_cases e2 : l = lc
    · subst e2
      rw [step_graph P.hc] at hs
      cases L with
      | nil =>
        rw [fire_comp_none (List.mem_cons_self) (hcs c0 List.mem_cons_self)] at hs; cases hs
      | cons v L' =>
        have hne : ∀ c ∈ c0 :: cr, σ c ≠ [] := fun c hc => by rw [hcs c hc]; simp
        rw [fire_comp hne] at hs
        have hu := (Option.some.inj hs).symm
        have hmap : (c0 :: cr).map (hd σ) = (c0 :: cr).map (fun _ => v) := by
          apply List.map_congr_left; intro c hc; simp [hd, hcs c hc]
        have hx' : σ' x = v :: (L' ++ σ x) := by rw [hx]; rfl
        have hs' : step (graph rs') σ' lf = some (applyF σ' (popOf [x],
            fun c => if c = y then [(allZero (c0 :: cr) g).eval ([x].map (hd σ'))] else [])) := by
          rw [step_graph P.hf', fire_comp (by intro c hc; simp at hc; subst hc; rw [hx']; simp)]; rfl
        refine ⟨_, 1, Run.cons lf hs' (Run.refl _), L', ?_, ?_, ?_, ?_⟩
        · intro c hc
          rw [hu, comp_at (fun h => P.hy (List.mem_cons_of_mem _ h)), comp_at (by simp [P.y_ne_x])]
          have h1 : c ≠ x := fun e => hc (by simp [e])
          have h2 : c ∉ c0 :: cr := fun h => hc (List.mem_cons_of_mem _ h)
          have h3 : c ∉ [x] := by simp [h1]
          simp only [h2, h3, ite_false]
          by_cases hcy : c = y
          · subst hcy
            simp only [ite_true, hA c hc, List.map_cons, List.map_nil, hd, hx', List.headD_cons,
              eval_allZero, hmap]
          · simp [hcy, hA c hc]
        · rw [hu, comp_at (fun h => P.hy (List.mem_cons_of_mem _ h)), comp_at (by simp [P.y_ne_x])]
          simp [P.x_nin, P.y_ne_x.symm, hx']
        · intro c hc
          rw [hu, comp_at (fun h => P.hy (List.mem_cons_of_mem _ h))]
          simp [hc, hcs c hc]
        · intro c hc
          rw [comp_at (by simp [P.y_ne_x])]
          have h1 : c ≠ x := fun e => P.x_nin (e ▸ hc)
          have h2 : c ≠ y := fun e => P.y_nin (e ▸ hc)
          simp [h1, h2, hcs' c hc]
    · cases hr : rs[l]? with
      | none => rw [none_none hr] at hs; cases hs
      | some r =>
        obtain ⟨hr', hrd⟩ := P.out e1 e2 hr
        obtain ⟨fr, hf, rfl, hs'⟩ := outside_step hr hr' hrd hA hs
        have hfr' : r.fire natVI σ' = some fr := by rw [fire_agree hA r hrd]; exact hf
        refine ⟨_, 1, Run.cons l hs' (Run.refl _), L, applyF_agree hA fr, ?_, ?_, ?_⟩
        · rw [applyF_app hf (nin_of hrd (by simp)), applyF_app hfr' (nin_of hrd (by simp)), hx, List.append_assoc]
        · intro c hc
          rw [applyF_app hf (nin_of hrd (List.mem_cons_of_mem _ hc)), hcs c hc,
            fire_push0 hf (fun h => P.houts l r e1 hr c h hc), List.append_nil]
        · intro c hc
          rw [applyF_app hfr' (nin_of hrd (List.mem_cons_of_mem _ hc)), hcs' c hc,
            fire_push0 hf (fun h => P.houts l r e1 hr c h hc), List.append_nil]

theorem fj_fwd_term (P : PatFJ rs rs' lf lc x y c0 cr g) :
    ∀ σ σ', RelFJ x c0 cr σ σ' → Terminal (step (graph rs)) σ →
      ∃ u' n, Run (step (graph rs')) σ' n u' ∧ Terminal (step (graph rs')) u' ∧ Agree (c0 :: cr) σ u' := by
  intro σ σ' ⟨L, hA, hx, hcs, hcs'⟩ hT
  have hx0 : σ x = [] := by
    cases hxv : σ x with
    | nil => rfl
    | cons v vs => have := hT lf; rw [step_graph P.hf, fire_fork hxv] at this; cases this
  have hL : L = [] := by
    cases L with
    | nil => rfl
    | cons v L' =>
      have hne : ∀ c ∈ c0 :: cr, σ c ≠ [] := fun c hc => by rw [hcs c hc]; simp
      have := hT lc; rw [step_graph P.hc, fire_comp hne] at this; cases this
  subst hL
  refine ⟨σ', 0, Run.refl _, ?_, ?_⟩
  · intro l
    by_cases e1 : l = lf
    · subst e1; rw [step_graph P.hf', fire_comp_none (List.mem_singleton_self x) (by rw [hx, hx0]; rfl)]; rfl
    · by_cases e2 : l = lc
      · subst e2; rw [step_graph P.hc', fire_sink_none (hcs' c0 List.mem_cons_self)]; rfl
      · cases hr : rs[l]? with
        | none => rw [← P.hsame l e1 e2] at hr; exact none_none hr σ'
        | some r =>
          obtain ⟨hr', hrd⟩ := P.out e1 e2 hr
          exact outside_none hr hr' hrd hA (hT l)
  · intro c hc
    by_cases e : c = x
    · subst e; rw [hx, hx0]; rfl
    · exact hA c (fun h => by rcases List.mem_cons.mp h with h | h; exact e h; exact hc h)

theorem fj_bwd_step (P : PatFJ rs rs' lf lc x y c0 cr g) :
    ∀ σ' σ l u', RelFJ x c0 cr σ σ' → step (graph rs') σ' l = some u' →
      ∃ u n, Run (step (graph rs)) σ n u ∧ RelFJ x c0 cr u u' := by
  intro σ' σ l u' hR hs
  obtain ⟨L, hA, hx, hcs, hcs'⟩ := hR
  by_cases e1 : l = lf
  · rw [e1] at hs
    rw [step_graph P.hf'] at hs
    cases hxv' : σ' x with
    | nil => rw [fire_comp_none (List.mem_singleton_self x) hxv'] at hs; cases hs
    | cons v rest =>
      rw [fire_comp (by intro c hc; simp at hc; subst hc; rw [hxv']; simp)] at hs
      have hu' := (Option.some.inj hs).symm
      -- after the step, σ' has `rest` on x and `g(v, ..., v)` appended on y
      -- reach the matching σ-store: fork once if nothing is pending, then the comp
      have key : ∀ (τ : Store Nat Nat) (L' : List Nat), Agree (x :: c0 :: cr) τ σ' → (∀ c ∈ c0 :: cr, τ c = v :: L') →
          σ' x = v :: (L' ++ τ x) → ∃ u n, Run (step (graph rs)) τ n u ∧ RelFJ x c0 cr u u' := by
        intro τ L' hAτ hcsτ hxτ
        have hne : ∀ c ∈ c0 :: cr, τ c ≠ [] := fun c hc => by rw [hcsτ c hc]; simp
        have hmap : (c0 :: cr).map (hd τ) = (c0 :: cr).map (fun _ => v) := by
          apply List.map_congr_left; intro c hc; simp [hd, hcsτ c hc]
        have hsτ : step (graph rs) τ lc = some (applyF τ (popOf (c0 :: cr),
            fun c => if c = y then [g.eval ((c0 :: cr).map (hd τ))] else [])) := by
          rw [step_graph P.hc, fire_comp hne]; rfl
        have hrest : rest = L' ++ τ x := by rw [hxτ] at hxv'; exact (List.cons.inj hxv').2.symm
        refine ⟨_, 1, Run.cons lc hsτ (Run.refl _), L', ?_, ?_, ?_, ?_⟩
        · intro c hc
          rw [hu', comp_at (fun h => P.hy (List.mem_cons_of_mem _ h)), comp_at (by simp [P.y_ne_x])]
          have h1 : c ≠ x := fun e => hc (by simp [e])
          have h2 : c ∉ c0 :: cr := fun h => hc (List.mem_cons_of_mem _ h)
          have h3 : c ∉ [x] := by simp [h1]
          simp only [h2, h3, ite_false]
          by_cases hcy : c = y
          · subst hcy
            simp only [ite_true, hAτ c hc, List.map_cons, List.map_nil, hd, hxv', List.headD_cons,
              eval_allZero, hmap]
          · simp [hcy, hAτ c hc]
        · rw [hu', comp_at (fun h => P.hy (List.mem_cons_of_mem _ h)), comp_at (by simp [P.y_ne_x])]
          simp [P.x_nin, P.y_ne_x.symm, hxv', hrest]
        · intro c hc
          rw [comp_at (fun h => P.hy (List.mem_cons_of_mem _ h))]
          simp [hc, hcsτ c hc]
        · intro c hc
          rw [hu', comp_at (by simp [P.y_ne_x])]
          have h1 : c ≠ x := fun e => P.x_nin (e ▸ hc)
          have h2 : c ≠ y := fun e => P.y_nin (e ▸ hc)
          simp [h1, h2, hcs' c hc]
      cases L with
      | cons w L' =>
        have hw : w = v := by rw [hx] at hxv'; exact (List.cons.inj hxv').1
        subst hw
        exact key σ L' hA hcs (by rw [hx]; rfl)
      | nil =>
        -- nothing pending: fork first
        have hxv : σ x = v :: rest := by rw [← hxv', hx]; rfl
        have hsf : step (graph rs) σ lf = some (applyF σ (popOf [x],
            fun c => if c ∈ c0 :: cr then [v] else [])) := by
          rw [step_graph P.hf, fire_fork hxv]; rfl
        let τ := applyF σ (popOf [x], fun c => if c ∈ c0 :: cr then [v] else [])
        have hAτ : Agree (x :: c0 :: cr) τ σ' := by
          intro c hc
          have h1 : c ≠ x := fun e => hc (by simp [e])
          have h2 : c ∉ c0 :: cr := fun h => hc (List.mem_cons_of_mem _ h)
          simp only [τ, fork_at P.x_nin, h1, h2, ite_false]; exact hA c hc
        have hcsτ : ∀ c ∈ c0 :: cr, τ c = v :: [] := by
          intro c hc
          have h1 : c ≠ x := fun e => P.x_nin (e ▸ hc)
          simp only [τ, fork_at P.x_nin, h1, hc, ite_false, ite_true, hcs c hc]; rfl
        have hxτ : σ' x = v :: ([] ++ τ x) := by
          simp only [τ, fork_at P.x_nin, ite_true, hxv, List.tail_cons, List.nil_append]; exact hxv'
        obtain ⟨u, n, hrun, hR⟩ := key τ [] hAτ hcsτ hxτ
        exact ⟨u, n + 1, Run.cons lf hsf hrun, hR⟩
  · by_cases e2 : l = lc
    · subst e2; rw [step_graph P.hc', fire_sink_none (hcs' c0 List.mem_cons_self)] at hs; cases hs
    · cases hr' : rs'[l]? with
      | none => rw [none_none hr'] at hs; cases hs
      | some r =>
        have hr : rs[l]? = some r := by rw [← P.hsame l e1 e2, hr']
        obtain ⟨-, hrd⟩ := P.out e1 e2 hr
        obtain ⟨fr, hf', rfl, hs2⟩ := outside_step hr' hr hrd hA.symm hs
        have hf : r.fire natVI σ = some fr := by rw [← fire_agree hA r hrd]; exact hf'
        refine ⟨_, 1, Run.cons l hs2 (Run.refl _), L, applyF_agree hA fr, ?_, ?_, ?_⟩
        · rw [applyF_app hf (nin_of hrd (by simp)), applyF_app hf' (nin_of hrd (by simp)), hx, List.append_assoc]
        · intro c hc
          rw [applyF_app hf (nin_of hrd (List.mem_cons_of_mem _ hc)), hcs c hc,
            fire_push0 hf (fun h => P.houts l r e1 hr c h hc), List.append_nil]
        · intro c hc
          rw [applyF_app hf' (nin_of hrd (List.mem_cons_of_mem _ hc)), hcs' c hc,
            fire_push0 hf (fun h => P.houts l r e1 hr c h hc), List.append_nil]

theorem fj_bwd_term (P : PatFJ rs rs' lf lc x y c0 cr g) :
    ∀ σ' σ, RelFJ x c0 cr σ σ' → Terminal (step (graph rs')) σ' →
      ∃ u n, Run (step (graph rs)) σ n u ∧ Terminal (step (graph rs)) u ∧ Agree (c0 :: cr) σ' u := by
  intro σ' σ ⟨L, hA, hx, hcs, hcs'⟩ hT
  have hx0 : σ' x = [] := by
    cases hxv : σ' x with
    | nil => rfl
    | cons v vs =>
      have := hT lf
      rw [step_graph P.hf', fire_comp (by intro c hc; simp at hc; subst hc; rw [hxv]; simp)] at this; cases this
  rw [hx] at hx0
  have hL : L = [] := (List.append_eq_nil_iff.mp hx0).1
  have hσx : σ x = [] := (List.append_eq_nil_iff.mp hx0).2
  subst hL
  refine ⟨σ, 0, Run.refl _, ?_, ?_⟩
  · intro l
    by_cases e1 : l = lf
    · subst e1; rw [step_graph P.hf, fire_fork_none hσx]; rfl
    · by_cases e2 : l = lc
      · subst e2; rw [step_graph P.hc, fire_comp_none List.mem_cons_self (hcs c0 List.mem_cons_self)]; rfl
      · cases hr : rs[l]? with
        | none => exact none_none hr σ
        | some r =>
          obtain ⟨hr', hrd⟩ := P.out e1 e2 hr
          exact outside_none hr' hr hrd hA.symm (hT l)
  · intro c hc
    by_cases e : c = x
    · subst e; rw [hx, hσx]; rfl
    · exact (hA c (fun h => by rcases List.mem_cons.mp h with h | h; exact e h; exact hc h)).symm

theorem relFJ_init {σ0 : Store Nat Nat} (h0 : ∀ c ∈ c0 :: cr, σ0 c = []) :
    RelFJ x c0 cr σ0 σ0 := ⟨[], fun _ _ => rfl, rfl, h0, h0⟩

/-- Every complete run of the fork + comp graph has a complete run of the one-comp graph, same store outside the
fork's outputs. -/
theorem fj_forward (P : PatFJ rs rs' lf lc x y c0 cr g) {σ0 t : Store Nat Nat} {n : Nat}
    (h0 : ∀ c ∈ c0 :: cr, σ0 c = []) (hr : Run (step (graph rs)) σ0 n t) (ht : Terminal (step (graph rs)) t) :
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧ Agree (c0 :: cr) t t' :=
  sim_complete (RelFJ x c0 cr) (Agree (c0 :: cr)) (fj_fwd_step P) (fj_fwd_term P) hr ht σ0 (relFJ_init h0)

theorem fj_backward (P : PatFJ rs rs' lf lc x y c0 cr g) {σ0 t' : Store Nat Nat} {n : Nat}
    (h0 : ∀ c ∈ c0 :: cr, σ0 c = []) (hr : Run (step (graph rs')) σ0 n t') (ht : Terminal (step (graph rs')) t') :
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧ Agree (c0 :: cr) t' t :=
  sim_complete (fun σ' σ => RelFJ x c0 cr σ σ') (Agree (c0 :: cr))
    (fun σ' σ l u' hR hs => fj_bwd_step P σ' σ l u' hR hs) (fun σ' σ hR hT => fj_bwd_term P σ' σ hR hT)
    hr ht σ0 (relFJ_init h0)

end FJ

end Formal.Rewrite.Steps
