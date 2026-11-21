import Formal.Rewrite.Steps.Cong

/-!
# Formal.Rewrite.Steps.Dedupe — a comp reading two copies of one forked value reads one (shard A, 2026-11-19)

**Problem, plainly.** A fork copies `x` onto `a` and `b` (among others), and one comp reads both `a` and `b`. Is it the
same, whatever surrounds it, to drop `b` from the fork and let the comp use `a` where it used `b`? Unfused code
shares a value through forks; a fused region reads it once. This step is what makes the two comparable.

**Proved** (`dd_forward`, `dd_backward`): for ANY imported graph `rs` holding `fork x os` at `lf` (with `a, b ∈ os`)
and `comp ins y F` at `lc` (with `a, b ∈ ins`), and `rs'` equal except `fork x (os.erase b)` at `lf` and
`comp (ins.erase b) y (dedupE ins a b F)` at `lc`, with `os` and `ins` duplicate-free, `a ≠ b`, `x ∉ os`, `y ∉ ins`,
no other rule reading `a` or `b`, and no other rule writing them: from any store with `a, b` empty, every complete run
of either graph is matched by a complete run of the other ending in the same store outside `b`. (`lockstep`: the
two graphs fire the same labels in the same order.)

**Not covered:** token level only.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

/-! ## Lockstep simulation -/

/-- `R` relates two stores so that every label fires in both or in neither, into related stores. -/
def Lockstep (rs rs' : List Rule) (R : Store Nat Nat → Store Nat Nat → Prop) : Prop :=
  ∀ σ σ' l, R σ σ' →
    (step (graph rs) σ l = none ↔ step (graph rs') σ' l = none) ∧
    (∀ u, step (graph rs) σ l = some u → ∃ u', step (graph rs') σ' l = some u' ∧ R u u') ∧
    (∀ u', step (graph rs') σ' l = some u' → ∃ u, step (graph rs) σ l = some u ∧ R u u')

theorem lockstep_fwd {rs rs' : List Rule} {R : Store Nat Nat → Store Nat Nat → Prop} (h : Lockstep rs rs' R) :
    ∀ {σ t n}, Run (step (graph rs)) σ n t → ∀ σ', R σ σ' → ∃ t', Run (step (graph rs')) σ' n t' ∧ R t t' := by
  intro σ t n hr
  induction hr with
  | refl s => intro σ' hR; exact ⟨σ', Run.refl _, hR⟩
  | cons l hl _ ih =>
    intro σ' hR
    obtain ⟨u', hu', hRu⟩ := (h _ _ l hR).2.1 _ hl
    obtain ⟨t', hr', hRt⟩ := ih u' hRu
    exact ⟨t', Run.cons l hu' hr', hRt⟩

theorem lockstep_bwd {rs rs' : List Rule} {R : Store Nat Nat → Store Nat Nat → Prop} (h : Lockstep rs rs' R) :
    ∀ {σ' t' n}, Run (step (graph rs')) σ' n t' → ∀ σ, R σ σ' → ∃ t, Run (step (graph rs)) σ n t ∧ R t t' := by
  intro σ' t' n hr
  induction hr with
  | refl s => intro σ hR; exact ⟨σ, Run.refl _, hR⟩
  | cons l hl _ ih =>
    intro σ hR
    obtain ⟨u, hu, hRu⟩ := (h _ _ l hR).2.2 _ hl
    obtain ⟨t, hr', hRt⟩ := ih u hRu
    exact ⟨t, Run.cons l hu hr', hRt⟩

theorem lockstep_term {rs rs' : List Rule} {R : Store Nat Nat → Store Nat Nat → Prop} (h : Lockstep rs rs' R)
    {σ σ' : Store Nat Nat} (hR : R σ σ') : Terminal (step (graph rs)) σ ↔ Terminal (step (graph rs')) σ' :=
  ⟨fun hT l => (h σ σ' l hR).1.mp (hT l), fun hT l => (h σ σ' l hR).1.mpr (hT l)⟩

/-! ## The deduplicated expression -/

/-- `F` over `ins`, re-indexed over `ins.erase b`, with input `b` read from `a`. -/
def dedupE (ins : List Nat) (a b : Nat) (F : E) : E :=
  F.subst (ins.map fun c => .var (pos (ins.erase b) (if c = b then a else c)))

theorem mem_erase_of_ne' {l : List Nat} {a b : Nat} (h : a ∈ l) (hab : a ≠ b) : a ∈ l.erase b :=
  (List.mem_erase_of_ne hab).mpr h

theorem eval_dedupE {ins : List Nat} {a b : Nat} (F : E) (ha : a ∈ ins) (hab : a ≠ b) (h : Nat → Nat)
    (hh : h b = h a) : (dedupE ins a b F).eval ((ins.erase b).map h) = F.eval (ins.map h) := by
  simp only [dedupE, eval_subst, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  simp only [Function.comp, E.eval]
  by_cases e : c = b
  · subst e; simp only [ite_true]; rw [getD_pos h _ (mem_erase_of_ne' ha hab), hh]
  · simp only [e, ite_false]; exact getD_pos h _ (mem_erase_of_ne' hc e)

/-! ## The pattern -/

structure PatDD (rs rs' : List Rule) (lf lc x y a b : Nat) (os ins : List Nat) (F : E) : Prop where
  hf : rs[lf]? = some (.fork x os)
  hc : rs[lc]? = some (.comp ins y F)
  hf' : rs'[lf]? = some (.fork x (os.erase b))
  hc' : rs'[lc]? = some (.comp (ins.erase b) y (dedupE ins a b F))
  hsame : ∀ l, l ≠ lf → l ≠ lc → rs'[l]? = rs[l]?
  hins : ∀ l r, l ≠ lc → rs[l]? = some r → a ∉ r.insL ∧ b ∉ r.insL
  houts : ∀ l r, l ≠ lf → rs[l]? = some r → a ∉ r.outsL ∧ b ∉ r.outsL
  hao : a ∈ os
  hbo : b ∈ os
  hai : a ∈ ins
  hbi : b ∈ ins
  hab : a ≠ b
  hosnd : os.Nodup
  hinsnd : ins.Nodup
  hx : x ∉ os
  hy : y ∉ ins

section DD
variable {rs rs' : List Rule} {lf lc x y a b : Nat} {os ins : List Nat} {F : E}

def RelDD (a b : Nat) (σ σ' : Store Nat Nat) : Prop := Agree [b] σ σ' ∧ σ' b = [] ∧ σ b = σ a

theorem PatDD.lfc (P : PatDD rs rs' lf lc x y a b os ins F) : lf ≠ lc := fun h => by
  have := P.hf; rw [h, P.hc] at this; cases this

theorem dd_lockstep (P : PatDD rs rs' lf lc x y a b os ins F) : Lockstep rs rs' (RelDD a b) := by
  intro σ σ' l ⟨hA, hb', hab⟩
  have hxb : x ≠ b := fun e => P.hx (e ▸ P.hbo)
  have hxa : x ≠ a := fun e => P.hx (e ▸ P.hao)
  have hσx : σ' x = σ x := hA x (by simp [hxb])
  have hyb : y ≠ b := fun e => P.hy (e ▸ P.hbi)
  by_cases e1 : l = lf
  · subst e1
    rw [step_graph P.hf, step_graph P.hf']
    cases hv : σ x with
    | nil =>
      rw [fire_fork_none hv, fire_fork_none (by rw [hσx, hv])]
      exact ⟨by simp, fun u h => (by cases h), fun u h => (by cases h)⟩
    | cons v vs =>
      rw [fire_fork hv, fire_fork (by rw [hσx, hv])]
      have hx' : x ∉ os.erase b := fun h => P.hx (List.mem_of_mem_erase h)
      have rel : RelDD a b (applyF σ (popOf [x], fun c => if c ∈ os then [v] else []))
          (applyF σ' (popOf [x], fun c => if c ∈ os.erase b then [v] else [])) := by
        refine ⟨?_, ?_, ?_⟩
        · intro c hc
          have hcb : c ≠ b := by simpa using hc
          rw [fork_at P.hx, fork_at hx']
          by_cases cx : c = x
          · subst cx; simp [hσx]
          · have : c ∈ os.erase b ↔ c ∈ os := List.mem_erase_of_ne hcb
            simp only [cx, ite_false, this, hA c hc]
        · rw [fork_at hx']; simp [hxb.symm, hb', P.hosnd.not_mem_erase]
        · rw [fork_at P.hx, fork_at P.hx]; simp [hxb.symm, hxa.symm, P.hbo, P.hao, hab]
      exact ⟨by simp, fun u h => ⟨_, rfl, (Option.some.inj h) ▸ rel⟩,
        fun u' h => ⟨_, rfl, (Option.some.inj h) ▸ rel⟩⟩
  · by_cases e2 : l = lc
    · subst e2
      rw [step_graph P.hc, step_graph P.hc']
      have hyi : y ∉ ins.erase b := fun h => P.hy (List.mem_of_mem_erase h)
      by_cases hall : ∀ c ∈ ins, σ c ≠ []
      · have hall' : ∀ c ∈ ins.erase b, σ' c ≠ [] := by
          intro c hc
          have hcb : c ≠ b := fun e => P.hinsnd.not_mem_erase (e ▸ hc)
          rw [hA c (by simp [hcb])]; exact hall c (List.mem_of_mem_erase hc)
        rw [fire_comp hall, fire_comp hall']
        have hmap : (ins.erase b).map (hd σ') = (ins.erase b).map (hd σ) := by
          apply List.map_congr_left; intro c hc
          have hcb : c ≠ b := fun e => P.hinsnd.not_mem_erase (e ▸ hc)
          simp only [hd]; rw [hA c (by simp [hcb])]
        have hval : (dedupE ins a b F).eval ((ins.erase b).map (hd σ')) = F.eval (ins.map (hd σ)) := by
          rw [hmap]; exact eval_dedupE F P.hai P.hab (hd σ) (by simp [hd, hab])
        have rel : RelDD a b (applyF σ (popOf ins, fun c => if c = y then [F.eval (ins.map (hd σ))] else []))
            (applyF σ' (popOf (ins.erase b), fun c => if c = y then
              [(dedupE ins a b F).eval ((ins.erase b).map (hd σ'))] else [])) := by
          refine ⟨?_, ?_, ?_⟩
          · intro c hc
            have hcb : c ≠ b := by simpa using hc
            rw [comp_at P.hy, comp_at hyi, hval]
            have : c ∈ ins.erase b ↔ c ∈ ins := List.mem_erase_of_ne hcb
            simp only [this, hA c hc]
          · rw [comp_at hyi]; simp [P.hinsnd.not_mem_erase, hyb.symm, hb']
          · rw [comp_at P.hy, comp_at P.hy]; simp [P.hbi, P.hai, hab]
        exact ⟨by simp, fun u h => ⟨_, rfl, (Option.some.inj h) ▸ rel⟩,
          fun u' h => ⟨_, rfl, (Option.some.inj h) ▸ rel⟩⟩
      · obtain ⟨c, hc, he⟩ := exists_empty hall
        have hn : (Rule.comp ins y F).fire natVI σ = none := fire_comp_none hc he
        have hn' : (Rule.comp (ins.erase b) y (dedupE ins a b F)).fire natVI σ' = none := by
          by_cases hcb : c = b
          · subst hcb
            exact fire_comp_none (mem_erase_of_ne' P.hai P.hab) (by rw [hA a (by simp [P.hab]), ← hab, he])
          · exact fire_comp_none (mem_erase_of_ne' hc hcb) (by rw [hA c (by simp [hcb]), he])
        rw [hn, hn']
        exact ⟨by simp, fun u h => (by cases h), fun u h => (by cases h)⟩
    · -- outside rules: same rule, reads neither a nor b; fires identically
      have hs := P.hsame l e1 e2
      cases hr : rs[l]? with
      | none =>
        rw [none_none hr, none_none (by rw [hs, hr])]
        exact ⟨by simp, fun u h => (by cases h), fun u h => (by cases h)⟩
      | some r =>
        have hr' : rs'[l]? = some r := by rw [hs, hr]
        have hrd : ∀ c ∈ r.insL, c ∉ [b] := fun c hc h => by
          simp at h; subst h; exact (P.hins l r e2 hr).2 hc
        rw [step_graph hr, step_graph hr', fire_agree hA r hrd]
        cases hf : r.fire natVI σ with
        | none => exact ⟨by simp, fun u h => (by cases h), fun u h => (by cases h)⟩
        | some fr =>
          have rel : RelDD a b (applyF σ fr) (applyF σ' fr) := by
            refine ⟨applyF_agree hA fr, ?_, ?_⟩
            · rw [applyF_app (by rw [fire_agree hA r hrd]; exact hf) (P.hins l r e2 hr).2,
                fire_push0 hf (P.houts l r e1 hr).2, hb']; rfl
            · rw [applyF_app hf (P.hins l r e2 hr).2, applyF_app hf (P.hins l r e2 hr).1,
                fire_push0 hf (P.houts l r e1 hr).2, fire_push0 hf (P.houts l r e1 hr).1, hab]
          exact ⟨by simp, fun u h => ⟨_, rfl, (Option.some.inj h) ▸ rel⟩,
            fun u' h => ⟨_, rfl, (Option.some.inj h) ▸ rel⟩⟩

theorem dd_forward (P : PatDD rs rs' lf lc x y a b os ins F) {σ0 t : Store Nat Nat} {n : Nat}
    (ha0 : σ0 a = []) (hb0 : σ0 b = []) (hr : Run (step (graph rs)) σ0 n t) (ht : Terminal (step (graph rs)) t) :
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧ Agree [b] t t' := by
  obtain ⟨t', hr', hR⟩ := lockstep_fwd (dd_lockstep P) hr σ0 ⟨fun _ _ => rfl, hb0, by rw [ha0, hb0]⟩
  exact ⟨t', n, hr', (lockstep_term (dd_lockstep P) hR).mp ht, hR.1⟩

theorem dd_backward (P : PatDD rs rs' lf lc x y a b os ins F) {σ0 t' : Store Nat Nat} {n : Nat}
    (ha0 : σ0 a = []) (hb0 : σ0 b = []) (hr : Run (step (graph rs')) σ0 n t')
    (ht : Terminal (step (graph rs')) t') :
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧ Agree [b] t' t := by
  obtain ⟨t, hr0, hR⟩ := lockstep_bwd (dd_lockstep P) hr σ0 ⟨fun _ _ => rfl, hb0, by rw [ha0, hb0]⟩
  exact ⟨t, n, hr0, (lockstep_term (dd_lockstep P) hR).mpr ht, hR.1.symm⟩

end DD

end Formal.Rewrite.Steps
