import Formal.Rewrite.Steps.Cong

/-!
# Formal.Rewrite.Steps.Wire — a one-output fork is a wire (shard A, 2026-11-19)

**Problem, plainly.** A fork with a single output `a` copies `x` onto `a`, and one comp reads `a` (among other
inputs). Is it the same, whatever surrounds it, to delete the fork and let the comp read `x`?

**Proved** (`w_forward`, `w_backward`): for ANY imported graph `rs` holding `fork x [a]` at `lf` and `comp ins y F` at
`lc` with `a ∈ ins`, and `rs'` equal except the dead rule `sink a` at `lf` and `comp (ins with a replaced by x) y F`
at `lc`, with `ins` duplicate-free, `x ∉ ins`, `x ≠ a`, `y ∉ x :: ins`, no other rule reading `x` or `a`, and no other
rule writing `a`: from any store with `a` empty, every complete run of either graph is matched by a complete run of the
other ending in the same store outside `x` and `a`.

**Not covered:** token level only.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

def swA (a x : Nat) (c : Nat) : Nat := if c = a then x else c

structure PatW (rs rs' : List Rule) (lf lc x a y : Nat) (ins : List Nat) (F : E) : Prop where
  hf : rs[lf]? = some (.fork x [a])
  hc : rs[lc]? = some (.comp ins y F)
  hf' : rs'[lf]? = some (.sink a)
  hc' : rs'[lc]? = some (.comp (ins.map (swA a x)) y F)
  hsame : ∀ l, l ≠ lf → l ≠ lc → rs'[l]? = rs[l]?
  hins : ∀ l r, l ≠ lf → l ≠ lc → rs[l]? = some r → x ∉ r.insL ∧ a ∉ r.insL
  houts : ∀ l r, l ≠ lf → rs[l]? = some r → a ∉ r.outsL
  hai : a ∈ ins
  hnd : ins.Nodup
  hxi : x ∉ ins
  hxa : x ≠ a
  hy : y ∉ x :: ins

section W
variable {rs rs' : List Rule} {lf lc x a y : Nat} {ins : List Nat} {F : E}

def RelW (x a : Nat) (σ σ' : Store Nat Nat) : Prop :=
  Agree [x, a] σ σ' ∧ σ' x = σ a ++ σ x ∧ σ' a = []

section Facts
variable (P : PatW rs rs' lf lc x a y ins F)
include P
theorem PatW.lfc : lf ≠ lc := fun h => by have := P.hf; rw [h, P.hc] at this; cases this
theorem PatW.yx : y ≠ x := fun e => P.hy (by simp [e])
theorem PatW.yi : y ∉ ins := fun h => P.hy (List.mem_cons_of_mem _ h)
theorem PatW.ya : y ≠ a := fun e => P.yi (e ▸ P.hai)
theorem PatW.yi' : y ∉ ins.map (swA a x) := by
  intro h
  obtain ⟨c, hc, he⟩ := List.mem_map.mp h
  unfold swA at he
  split at he
  · exact P.yx he.symm
  · exact P.yi (he ▸ hc)
theorem PatW.x_mem' : x ∈ ins.map (swA a x) := List.mem_map.mpr ⟨a, P.hai, by simp [swA]⟩
theorem PatW.a_nmem' : a ∉ ins.map (swA a x) := by
  intro h
  obtain ⟨c, hc, he⟩ := List.mem_map.mp h
  unfold swA at he
  split at he
  · exact P.hxa he
  · rename_i hne; exact hne he
/-- Membership in the rewired input list, for channels other than `x` and `a`. -/
theorem PatW.mem' {c : Nat} (hcx : c ≠ x) (hca : c ≠ a) : c ∈ ins.map (swA a x) ↔ c ∈ ins := by
  constructor
  · intro h
    obtain ⟨d, hd, he⟩ := List.mem_map.mp h
    unfold swA at he
    split at he
    · exact absurd he.symm hcx
    · exact he ▸ hd
  · intro h; exact List.mem_map.mpr ⟨c, h, by simp [swA, hca]⟩
end Facts

theorem PatW.out (P : PatW rs rs' lf lc x a y ins F) {l : Nat} {r : Rule} (h1 : l ≠ lf) (h2 : l ≠ lc)
    (hr : rs[l]? = some r) : rs'[l]? = some r ∧ ∀ c ∈ r.insL, c ∉ [x, a] := by
  refine ⟨by rw [P.hsame l h1 h2, hr], fun c hc hD => ?_⟩
  have := P.hins l r h1 h2 hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl
  · exact this.1 hc
  · exact this.2 hc

/-- With the relation, the rewired comp sees the same heads as the original (when `a` has a token in `σ`). -/
theorem heads_w (P : PatW rs rs' lf lc x a y ins F) {σ σ' : Store Nat Nat} (hR : RelW x a σ σ') (hne : σ a ≠ []) :
    (ins.map (swA a x)).map (hd σ') = ins.map (hd σ) := by
  obtain ⟨hA, hx, -⟩ := hR
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  simp only [Function.comp, swA]
  by_cases e : c = a
  · subst e; simp only [ite_true, hd, hx]
    cases h : σ c with
    | nil => exact absurd h hne
    | cons v vs => simp
  · simp only [e, ite_false, hd]
    have hcx : c ≠ x := fun h => P.hxi (h ▸ hc)
    rw [hA c (by simp [hcx, e])]

theorem w_fwd_step (P : PatW rs rs' lf lc x a y ins F) :
    ∀ σ σ' l u, RelW x a σ σ' → step (graph rs) σ l = some u →
      ∃ u' n, Run (step (graph rs')) σ' n u' ∧ RelW x a u u' := by
  intro σ σ' l u hR hs
  obtain ⟨hA, hx, ha'⟩ := hR
  by_cases e1 : l = lf
  · rw [e1, step_graph P.hf] at hs
    cases hv : σ x with
    | nil => rw [fire_fork_none hv] at hs; cases hs
    | cons v vs =>
      rw [fire_fork hv] at hs
      have hu := (Option.some.inj hs).symm; subst hu
      have hxa1 : x ∉ [a] := by simp [P.hxa]
      refine ⟨σ', 0, Run.refl _, ?_, ?_, ha'⟩
      · intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
        rw [fork_at hxa1]; simp [hc.1, hc.2, hA c (by simp [hc.1, hc.2])]
      · rw [fork_at hxa1, fork_at hxa1, hx, hv]; simp [P.hxa, P.hxa.symm]
  · by_cases e2 : l = lc
    · rw [e2, step_graph P.hc] at hs
      by_cases hall : ∀ c ∈ ins, σ c ≠ []
      · rw [fire_comp hall] at hs
        have hu := (Option.some.inj hs).symm; subst hu
        have hne := hall a P.hai
        have hall' : ∀ c ∈ ins.map (swA a x), σ' c ≠ [] := by
          intro c hc
          by_cases cx : c = x
          · subst cx; rw [hx]; simp [hne]
          · have ca : c ≠ a := fun h => P.a_nmem' (h ▸ hc)
            rw [hA c (by simp [cx, ca])]; exact hall c ((P.mem' cx ca).mp hc)
        have hs' : step (graph rs') σ' lc = some (applyF σ' (popOf (ins.map (swA a x)),
            fun c => if c = y then [F.eval ((ins.map (swA a x)).map (hd σ'))] else [])) := by
          rw [step_graph P.hc', fire_comp hall']; rfl
        rw [heads_w P ⟨hA, hx, ha'⟩ hne] at hs'
        refine ⟨_, 1, Run.cons lc hs' (Run.refl _), ?_, ?_, ?_⟩
        · intro c hc
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
          simp only [comp_atv P.yi (F.eval (ins.map (hd σ))), comp_atv P.yi' (F.eval (ins.map (hd σ))), P.mem' hc.1 hc.2, hA c (by simp [hc.1, hc.2])]
        · simp only [comp_atv P.yi (F.eval (ins.map (hd σ))), comp_atv P.yi' (F.eval (ins.map (hd σ)))]
          simp only [P.x_mem', P.hai, P.hxi, ite_true, ite_false, P.yx.symm, P.ya.symm, hx]
          cases h : σ a with
          | nil => exact absurd h hne
          | cons v vs => simp
        · rw [comp_atv P.yi' (F.eval (ins.map (hd σ)))]; simp [P.a_nmem', P.ya.symm, ha']
      · obtain ⟨c, hc, he⟩ := exists_empty hall
        rw [fire_comp_none hc he] at hs; cases hs
    · cases hr : rs[l]? with
      | none => rw [none_none hr] at hs; cases hs
      | some r =>
        obtain ⟨hr', hrd⟩ := P.out e1 e2 hr
        obtain ⟨fr, hf, rfl, hs'⟩ := outside_step hr hr' hrd hA hs
        have hfr' : r.fire natVI σ' = some fr := by rw [fire_agree hA r hrd]; exact hf
        refine ⟨_, 1, Run.cons l hs' (Run.refl _), applyF_agree hA fr, ?_, ?_⟩
        · rw [applyF_app hf (nin_of hrd (by simp)), applyF_app hfr' (nin_of hrd (by simp)),
            applyF_app hf (nin_of hrd (by simp)), fire_push0 hf (P.houts l r e1 hr), hx]; simp
        · rw [applyF_app hfr' (nin_of hrd (by simp)), fire_push0 hf (P.houts l r e1 hr), ha']; rfl

theorem w_fwd_term (P : PatW rs rs' lf lc x a y ins F) :
    ∀ σ σ', RelW x a σ σ' → Terminal (step (graph rs)) σ →
      ∃ u' n, Run (step (graph rs')) σ' n u' ∧ Terminal (step (graph rs')) u' ∧ Agree [x, a] σ u' := by
  intro σ σ' hR hT
  obtain ⟨hA, hx, ha'⟩ := hR
  have hx0 : σ x = [] := by
    cases hv : σ x with
    | nil => rfl
    | cons v vs => have := hT lf; rw [step_graph P.hf, fire_fork hv] at this; cases this
  refine ⟨σ', 0, Run.refl _, ?_, hA⟩
  intro l
  by_cases e1 : l = lf
  · rw [e1, step_graph P.hf', fire_sink_none ha']; rfl
  · by_cases e2 : l = lc
    · rw [e2, step_graph P.hc']
      have hq := hT lc
      rw [step_graph P.hc] at hq
      by_cases hall : ∀ c ∈ ins, σ c ≠ []
      · rw [fire_comp hall] at hq; cases hq
      · obtain ⟨c, hc, he⟩ := exists_empty hall
        by_cases ca : c = a
        · subst ca; rw [fire_comp_none P.x_mem' (by rw [hx, he, hx0]; rfl)]; rfl
        · have cx : c ≠ x := fun h => P.hxi (h ▸ hc)
          rw [fire_comp_none ((P.mem' cx ca).mpr hc) (by rw [hA c (by simp [cx, ca]), he])]; rfl
    · cases hr : rs[l]? with
      | none => rw [← P.hsame l e1 e2] at hr; exact none_none hr σ'
      | some r =>
        obtain ⟨hr', hrd⟩ := P.out e1 e2 hr
        exact outside_none hr hr' hrd hA (hT l)

theorem w_bwd_step (P : PatW rs rs' lf lc x a y ins F) :
    ∀ σ' σ l u', RelW x a σ σ' → step (graph rs') σ' l = some u' →
      ∃ u n, Run (step (graph rs)) σ n u ∧ RelW x a u u' := by
  intro σ' σ l u' hR hs
  by_cases e1 : l = lf
  · obtain ⟨-, -, ha'⟩ := hR
    rw [e1, step_graph P.hf', fire_sink_none ha'] at hs; cases hs
  · by_cases e2 : l = lc
    · -- make a's front available in σ (fire the fork once if a is empty), then fire the comp in both
      have pre : ∃ τ n, Run (step (graph rs)) σ n τ ∧ RelW x a τ σ' ∧ τ a ≠ [] := by
        obtain ⟨hA, hx, ha'⟩ := hR
        rw [e2, step_graph P.hc'] at hs
        by_cases hall' : ∀ c ∈ ins.map (swA a x), σ' c ≠ []
        · have hx' := hall' x P.x_mem'
          cases ha : σ a with
          | cons v vs => exact ⟨σ, 0, Run.refl _, ⟨hA, hx, ha'⟩, by rw [ha]; simp⟩
          | nil =>
            rw [hx, ha, List.nil_append] at hx'
            cases hv : σ x with
            | nil => exact absurd hv hx'
            | cons v vs =>
              have hxa1 : x ∉ [a] := by simp [P.hxa]
              have hs1 : step (graph rs) σ lf = some (applyF σ (popOf [x], fun c => if c ∈ [a] then [v] else [])) := by
                rw [step_graph P.hf, fire_fork hv]; rfl
              refine ⟨_, 1, Run.cons lf hs1 (Run.refl _), ⟨?_, ?_, ha'⟩, ?_⟩
              · intro c hc
                simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
                rw [fork_at hxa1]; simp [hc.1, hc.2, hA c (by simp [hc.1, hc.2])]
              · rw [fork_at hxa1, fork_at hxa1, hx, ha, hv]; simp [P.hxa, P.hxa.symm]
              · rw [fork_at hxa1]; simp [P.hxa.symm, ha]
        · obtain ⟨c, hc, he⟩ := exists_empty hall'
          rw [fire_comp_none hc he] at hs; cases hs
      obtain ⟨τ, n1, hrun1, hRτ, hne⟩ := pre
      obtain ⟨hA, hx, ha'⟩ := hRτ
      rw [e2, step_graph P.hc'] at hs
      by_cases hall' : ∀ c ∈ ins.map (swA a x), σ' c ≠ []
      · rw [fire_comp hall'] at hs
        have hu' := (Option.some.inj hs).symm; subst hu'
        have hall : ∀ c ∈ ins, τ c ≠ [] := by
          intro c hc
          by_cases ca : c = a
          · subst ca; exact hne
          · have cx : c ≠ x := fun h => P.hxi (h ▸ hc)
            have := hall' c ((P.mem' cx ca).mpr hc)
            rwa [hA c (by simp [cx, ca])] at this
        have hs1 : step (graph rs) τ lc = some (applyF τ (popOf ins,
            fun c => if c = y then [F.eval (ins.map (hd τ))] else [])) := by
          rw [step_graph P.hc, fire_comp hall]; rfl
        rw [heads_w P ⟨hA, hx, ha'⟩ hne]
        refine ⟨_, n1 + 1, run_trans hrun1 (Run.cons lc hs1 (Run.refl _)), ?_, ?_, ?_⟩
        · intro c hc
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
          simp only [comp_atv P.yi (F.eval (ins.map (hd τ))), comp_atv P.yi' (F.eval (ins.map (hd τ))), P.mem' hc.1 hc.2, hA c (by simp [hc.1, hc.2])]
        · simp only [comp_atv P.yi (F.eval (ins.map (hd τ))), comp_atv P.yi' (F.eval (ins.map (hd τ)))]
          simp only [P.x_mem', P.hai, P.hxi, ite_true, ite_false, P.yx.symm, P.ya.symm, hx]
          cases h : τ a with
          | nil => exact absurd h hne
          | cons v vs => simp
        · rw [comp_atv P.yi' (F.eval (ins.map (hd τ)))]; simp [P.a_nmem', P.ya.symm, ha']
      · obtain ⟨c, hc, he⟩ := exists_empty hall'
        rw [fire_comp_none hc he] at hs; cases hs
    · obtain ⟨hA, hx, ha'⟩ := hR
      cases hr' : rs'[l]? with
      | none => rw [none_none hr'] at hs; cases hs
      | some r =>
        have hr : rs[l]? = some r := by rw [← P.hsame l e1 e2, hr']
        obtain ⟨-, hrd⟩ := P.out e1 e2 hr
        obtain ⟨fr, hf', rfl, hs2⟩ := outside_step hr' hr hrd hA.symm hs
        have hf : r.fire natVI σ = some fr := by rw [← fire_agree hA r hrd]; exact hf'
        refine ⟨_, 1, Run.cons l hs2 (Run.refl _), applyF_agree hA fr, ?_, ?_⟩
        · rw [applyF_app hf (nin_of hrd (by simp)), applyF_app hf' (nin_of hrd (by simp)),
            applyF_app hf (nin_of hrd (by simp)), fire_push0 hf (P.houts l r e1 hr), hx]; simp
        · rw [applyF_app hf' (nin_of hrd (by simp)), fire_push0 hf (P.houts l r e1 hr), ha']; rfl

theorem w_bwd_term (P : PatW rs rs' lf lc x a y ins F) :
    ∀ σ' σ, RelW x a σ σ' → Terminal (step (graph rs')) σ' →
      ∃ u n, Run (step (graph rs)) σ n u ∧ Terminal (step (graph rs)) u ∧ Agree [x, a] σ' u := by
  intro σ' σ hR hT
  obtain ⟨hA, hx, ha'⟩ := hR
  have hxa1 : x ∉ [a] := by simp [P.hxa]
  obtain ⟨n, hrun⟩ := drain_fork P.hf hxa1 (σ x) σ rfl
  let τ : Store Nat Nat := fun c => if c = x then [] else if c ∈ [a] then σ c ++ σ x else σ c
  have hτa : τ a = σ' x := by simp [τ, P.hxa.symm, hx]
  have hτx : τ x = [] := by simp [τ]
  have hAτ : Agree [x, a] τ σ' := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
    simp only [τ, hc.1, hc.2, ite_false, List.mem_singleton]; exact hA c (by simp [hc.1, hc.2])
  refine ⟨τ, n, hrun, ?_, fun c hc => (hAτ c hc).symm⟩
  intro l
  by_cases e1 : l = lf
  · rw [e1, step_graph P.hf, fire_fork_none hτx]; rfl
  · by_cases e2 : l = lc
    · rw [e2, step_graph P.hc]
      have hq := hT lc
      rw [step_graph P.hc'] at hq
      by_cases hall' : ∀ c ∈ ins.map (swA a x), σ' c ≠ []
      · rw [fire_comp hall'] at hq; cases hq
      · obtain ⟨c, hc, he⟩ := exists_empty hall'
        by_cases cx : c = x
        · subst cx; rw [fire_comp_none P.hai (by rw [hτa, he])]; rfl
        · have ca : c ≠ a := fun h => P.a_nmem' (h ▸ hc)
          rw [fire_comp_none ((P.mem' cx ca).mp hc) (by rw [← hAτ c (by simp [cx, ca]), he])]; rfl
    · cases hr : rs[l]? with
      | none => exact none_none hr τ
      | some r =>
        obtain ⟨hr', hrd⟩ := P.out e1 e2 hr
        exact outside_none hr' hr hrd hAτ.symm (hT l)

theorem w_forward (P : PatW rs rs' lf lc x a y ins F) {σ0 t : Store Nat Nat} {n : Nat}
    (h0 : σ0 a = []) (hr : Run (step (graph rs)) σ0 n t) (ht : Terminal (step (graph rs)) t) :
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧ Agree [x, a] t t' :=
  sim_complete (RelW x a) (Agree [x, a]) (w_fwd_step P) (w_fwd_term P) hr ht σ0
    ⟨fun _ _ => rfl, by rw [h0]; rfl, h0⟩

theorem w_backward (P : PatW rs rs' lf lc x a y ins F) {σ0 t' : Store Nat Nat} {n : Nat}
    (h0 : σ0 a = []) (hr : Run (step (graph rs')) σ0 n t') (ht : Terminal (step (graph rs')) t') :
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧ Agree [x, a] t' t :=
  sim_complete (fun σ' σ => RelW x a σ σ') (Agree [x, a])
    (fun σ' σ l u' hR hs => w_bwd_step P σ' σ l u' hR hs) (fun σ' σ hR hT => w_bwd_term P σ' σ hR hT)
    hr ht σ0 ⟨fun _ _ => rfl, by rw [h0]; rfl, h0⟩

end W

end Formal.Rewrite.Steps
