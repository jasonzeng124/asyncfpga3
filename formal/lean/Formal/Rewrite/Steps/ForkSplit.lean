import Formal.Rewrite.Steps.Basic

/-!
# Formal.Rewrite.Steps.ForkSplit — one fork is two cascaded forks (shard A, 2026-11-19)

**Problem, plainly.** A fork copies `x` onto the channels `a ++ b`. Is that the same, whatever surrounds it, as a
fork copying `x` onto a fresh channel `e` and onto `b`, followed by a fork copying `e` onto `a`?

**Proved** (`fs_forward`, `fs_backward`): for ANY imported graph `rs` holding `fork x (a ++ b)` at `lf`, and `rs'`
equal except `fork x (e :: b)` at `lf` and `fork e a` at a label `le` unused in `rs`, with `x, e, a, b` distinct, no
other rule reading `e`, and no other rule writing `e` or the channels of `a`: from any store with `e` empty, every
complete run of either graph is matched by a complete run of the other ending in the same store outside `e`.
(Other rules may read `a` and `b`.)

**Not covered:** token level only.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

structure PatFS (rs rs' : List Rule) (lf le x e : Nat) (a b : List Nat) : Prop where
  hf : rs[lf]? = some (.fork x (a ++ b))
  hf' : rs'[lf]? = some (.fork x (e :: b))
  he : rs[le]? = none
  he' : rs'[le]? = some (.fork e a)
  hsame : ∀ l, l ≠ lf → l ≠ le → rs'[l]? = rs[l]?
  hins : ∀ l r, l ≠ lf → rs[l]? = some r → e ∉ r.insL
  houts : ∀ l r, l ≠ lf → rs[l]? = some r → ∀ c ∈ r.outsL, c ∉ e :: a
  hnd : (x :: e :: (a ++ b)).Nodup

section FS
variable {rs rs' : List Rule} {lf le x e : Nat} {a b : List Nat}

/-- `σ` runs `rs` (one fork), `σ'` runs `rs'` (two forks); `L` is what the first fork has put on `e` and the
second not yet copied. -/
def RelFS (e : Nat) (a : List Nat) (σ σ' : Store Nat Nat) : Prop :=
  Agree (e :: a) σ σ' ∧ σ e = [] ∧ ∀ c ∈ a, σ c = σ' c ++ σ' e

theorem PatFS.lfe (P : PatFS rs rs' lf le x e a b) : lf ≠ le := fun h => by
  have := P.hf; rw [h, P.he] at this; cases this
theorem PatFS.x_nin (P : PatFS rs rs' lf le x e a b) : x ∉ a ++ b := by
  have := P.hnd; simp only [List.nodup_cons, List.mem_cons, not_or] at this; exact this.1.2
theorem PatFS.x_nin' (P : PatFS rs rs' lf le x e a b) : x ∉ e :: b := by
  have := P.hnd; simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at this ⊢
  exact ⟨this.1.1, this.1.2.2⟩
theorem PatFS.e_nin (P : PatFS rs rs' lf le x e a b) : e ∉ a ++ b := by
  have := P.hnd; simp only [List.nodup_cons] at this; exact this.2.1
theorem PatFS.e_ne_x (P : PatFS rs rs' lf le x e a b) : e ≠ x := by
  have := P.hnd; simp only [List.nodup_cons, List.mem_cons, not_or] at this; exact fun h => this.1.1 h.symm
theorem PatFS.e_nin_a (P : PatFS rs rs' lf le x e a b) : e ∉ a := fun h => P.e_nin (List.mem_append_left _ h)
theorem PatFS.e_nin_b (P : PatFS rs rs' lf le x e a b) : e ∉ b := fun h => P.e_nin (List.mem_append_right _ h)
theorem PatFS.ab (P : PatFS rs rs' lf le x e a b) {c : Nat} (h : c ∈ a) : c ∉ b := by
  have := P.hnd
  simp only [List.nodup_cons, List.nodup_append] at this
  exact fun hb => this.2.2.2.2 c h c hb rfl

/-- Drain the second fork: the store `σ'` becomes `σ`. -/
theorem fs_drain (P : PatFS rs rs' lf le x e a b) {σ σ' : Store Nat Nat} (hR : RelFS e a σ σ') :
    ∃ n, Run (step (graph rs')) σ' n σ := by
  obtain ⟨hA, he0, ha⟩ := hR
  obtain ⟨n, hrun⟩ := drain_fork P.he' P.e_nin_a (σ' e) σ' rfl
  refine ⟨n, ?_⟩
  have : (fun c => if c = e then [] else if c ∈ a then σ' c ++ σ' e else σ' c) = σ := by
    funext c
    by_cases h1 : c = e
    · subst h1; simp [he0]
    · by_cases h2 : c ∈ a
      · simp [h1, h2, ha c h2]
      · simp only [h1, h2, ite_false]
        exact hA c (fun h => by rcases List.mem_cons.mp h with h | h; exact h1 h; exact h2 h)
  rw [this] at hrun; exact hrun

theorem relFS_refl {σ : Store Nat Nat} (he0 : σ e = []) : RelFS e a σ σ :=
  ⟨fun _ _ => rfl, he0, fun c _ => by rw [he0, List.append_nil]⟩

theorem fs_fwd_step (P : PatFS rs rs' lf le x e a b) :
    ∀ σ σ' l u, RelFS e a σ σ' → step (graph rs) σ l = some u →
      ∃ u' n, Run (step (graph rs')) σ' n u' ∧ RelFS e a u u' := by
  intro σ σ' l u hR hs
  obtain ⟨hA, he0, ha⟩ := hR
  by_cases e1 : l = lf
  · rw [e1, step_graph P.hf] at hs
    cases hxv : σ x with
    | nil => rw [fire_fork_none hxv] at hs; cases hs
    | cons v vs =>
      rw [fire_fork hxv] at hs
      have hu := (Option.some.inj hs).symm
      have hx' : σ' x = v :: vs := by rw [hA x (fun h => by
        rcases List.mem_cons.mp h with h | h
        · exact P.e_ne_x h.symm
        · exact P.x_nin (List.mem_append_left _ h))]; exact hxv
      have hs' : step (graph rs') σ' lf = some (applyF σ' (popOf [x], fun c => if c ∈ e :: b then [v] else [])) := by
        rw [step_graph P.hf', fire_fork hx']; rfl
      refine ⟨_, 1, Run.cons lf hs' (Run.refl _), ?_, ?_, ?_⟩
      · intro c hc
        rw [hu, fork_at P.x_nin, fork_at P.x_nin']
        have h1 : c ≠ e := fun h => hc (by simp [h])
        have h2 : c ∉ a := fun h => hc (List.mem_cons_of_mem _ h)
        by_cases h3 : c = x
        · simp [h3, hx', hxv]
        · simp [h3, h1, h2, hA c hc]
      · rw [hu, fork_at P.x_nin]; simp [P.e_ne_x, P.e_nin, he0]
      · intro c hc
        have hue : applyF σ' (popOf [x], fun c => if c ∈ e :: b then [v] else []) e = σ' e ++ [v] := by
          rw [fork_at P.x_nin']; simp [P.e_ne_x]
        rw [hue]
        rw [hu, fork_at P.x_nin, fork_at P.x_nin']
        have h3 : c ≠ x := fun h => P.x_nin (h ▸ List.mem_append_left _ hc)
        have h1 : c ≠ e := fun h => P.e_nin_a (h ▸ hc)
        simp [h3, h1, hc, P.ab hc, ha c hc]
  · cases hr : rs[l]? with
    | none => rw [none_none hr] at hs; cases hs
    | some r =>
      have e2 : l ≠ le := fun h => by rw [h, P.he] at hr; cases hr
      have hr' : rs'[l]? = some r := by rw [P.hsame l e1 e2, hr]
      obtain ⟨n, hdr⟩ := fs_drain P ⟨hA, he0, ha⟩
      rw [step_graph hr] at hs
      cases hf : r.fire natVI σ with
      | none => rw [hf] at hs; cases hs
      | some fr =>
        rw [hf] at hs
        have hs' : step (graph rs') σ l = some u := by rw [step_graph hr', hf]; exact hs
        refine ⟨u, n + 1, run_trans hdr (Run.cons l hs' (Run.refl _)), relFS_refl ?_⟩
        rw [← (Option.some.inj hs), applyF_app hf (P.hins l r e1 hr), he0,
          fire_push0 hf (fun h => P.houts l r e1 hr e h (by simp))]; rfl

theorem fs_fwd_term (P : PatFS rs rs' lf le x e a b) :
    ∀ σ σ', RelFS e a σ σ' → Terminal (step (graph rs)) σ →
      ∃ u' n, Run (step (graph rs')) σ' n u' ∧ Terminal (step (graph rs')) u' ∧ Agree [e] σ u' := by
  intro σ σ' hR hT
  obtain ⟨n, hdr⟩ := fs_drain P hR
  refine ⟨σ, n, hdr, ?_, fun _ _ => rfl⟩
  intro l
  by_cases e1 : l = lf
  · have hx0 : σ x = [] := by
      cases hxv : σ x with
      | nil => rfl
      | cons v vs => have := hT lf; rw [step_graph P.hf, fire_fork hxv] at this; cases this
    rw [e1, step_graph P.hf', fire_fork_none hx0]; rfl
  · by_cases e2 : l = le
    · rw [e2, step_graph P.he', fire_fork_none hR.2.1]; rfl
    · have := hT l; rw [← this]
      cases hr : rs[l]? with
      | none =>
        have hr' : rs'[l]? = none := by rw [P.hsame l e1 e2]; exact hr
        rw [none_none hr, none_none hr']
      | some r => rw [step_graph hr, step_graph (by rw [P.hsame l e1 e2]; exact hr)]

theorem fs_bwd_step (P : PatFS rs rs' lf le x e a b) :
    ∀ σ' σ l u', RelFS e a σ σ' → step (graph rs') σ' l = some u' →
      ∃ u n, Run (step (graph rs)) σ n u ∧ RelFS e a u u' := by
  intro σ' σ l u' hR hs
  obtain ⟨hA, he0, ha⟩ := hR
  by_cases e1 : l = lf
  · rw [e1, step_graph P.hf'] at hs
    cases hxv' : σ' x with
    | nil => rw [fire_fork_none hxv'] at hs; cases hs
    | cons v vs =>
      rw [fire_fork hxv'] at hs
      have hu' := (Option.some.inj hs).symm
      have hxv : σ x = v :: vs := by rw [← hA x (fun h => by
        rcases List.mem_cons.mp h with h | h
        · exact P.e_ne_x h.symm
        · exact P.x_nin (List.mem_append_left _ h))]; exact hxv'
      have hs1 : step (graph rs) σ lf = some (applyF σ (popOf [x], fun c => if c ∈ a ++ b then [v] else [])) := by
        rw [step_graph P.hf, fire_fork hxv]; rfl
      refine ⟨_, 1, Run.cons lf hs1 (Run.refl _), ?_, ?_, ?_⟩
      · intro c hc
        rw [hu', fork_at P.x_nin, fork_at P.x_nin']
        have h1 : c ≠ e := fun h => hc (by simp [h])
        have h2 : c ∉ a := fun h => hc (List.mem_cons_of_mem _ h)
        by_cases h3 : c = x
        · simp [h3, hxv, hxv']
        · simp [h3, h1, h2, hA c hc]
      · rw [fork_at P.x_nin]; simp [P.e_ne_x, P.e_nin, he0]
      · intro c hc
        have hue : applyF σ' (popOf [x], fun c => if c ∈ e :: b then [v] else []) e = σ' e ++ [v] := by
          rw [fork_at P.x_nin']; simp [P.e_ne_x]
        rw [hu', hue, fork_at P.x_nin, fork_at P.x_nin']
        have h3 : c ≠ x := fun h => P.x_nin (h ▸ List.mem_append_left _ hc)
        have h1 : c ≠ e := fun h => P.e_nin_a (h ▸ hc)
        simp [h3, h1, hc, P.ab hc, ha c hc]
  · by_cases e2 : l = le
    · rw [e2, step_graph P.he'] at hs
      cases hev : σ' e with
      | nil => rw [fire_fork_none hev] at hs; cases hs
      | cons v vs =>
        rw [fire_fork hev] at hs
        have hu' := (Option.some.inj hs).symm
        refine ⟨σ, 0, Run.refl _, ?_, he0, ?_⟩
        · intro c hc
          rw [hu', fork_at P.e_nin_a]
          have h1 : c ≠ e := fun h => hc (by simp [h])
          have h2 : c ∉ a := fun h => hc (List.mem_cons_of_mem _ h)
          simp [h1, h2, hA c hc]
        · intro c hc
          rw [hu', fork_at P.e_nin_a, fork_at P.e_nin_a]
          have h1 : c ≠ e := fun h => P.e_nin_a (h ▸ hc)
          simp [h1, hc, ha c hc, hev]
    · cases hr' : rs'[l]? with
      | none => rw [none_none hr'] at hs; cases hs
      | some r =>
        have hr : rs[l]? = some r := by rw [← P.hsame l e1 e2, hr']
        have hext : ∀ c ∈ r.insL, ∃ z, σ c = σ' c ++ z := by
          intro c hc
          by_cases h2 : c ∈ a
          · exact ⟨_, ha c h2⟩
          · have h1 : c ≠ e := fun h => P.hins l r e1 hr (h ▸ hc)
            exact ⟨[], by rw [List.append_nil, hA c (fun h => by
              rcases List.mem_cons.mp h with h | h; exact h1 h; exact h2 h)]⟩
        obtain ⟨fr, hf', hf, rfl, hs2⟩ := outside_step_ext hr hr' hext hs
        refine ⟨_, 1, Run.cons l hs2 (Run.refl _), applyF_agree hA fr, ?_, ?_⟩
        · rw [applyF_app hf (P.hins l r e1 hr), he0, fire_push0 hf (fun h => P.houts l r e1 hr e h (by simp))]; rfl
        · intro c hc
          have hpush : fr.2 c = [] := fire_push0 hf (fun h => P.houts l r e1 hr c h (List.mem_cons_of_mem _ hc))
          have hpe : fr.2 e = [] := fire_push0 hf (fun h => P.houts l r e1 hr e h (by simp))
          have hle : fr.1 c ≤ (σ' c).length := (r.node natVI).pop_le σ' fr c hf'
          rw [applyF_at, applyF_at, applyF_at, ha c hc, drop_app_of_le hle, hpush, hpe,
            fire_pop0 hf' (P.hins l r e1 hr)]
          simp

theorem fs_bwd_term (P : PatFS rs rs' lf le x e a b) :
    ∀ σ' σ, RelFS e a σ σ' → Terminal (step (graph rs')) σ' →
      ∃ u n, Run (step (graph rs)) σ n u ∧ Terminal (step (graph rs)) u ∧ Agree [e] σ' u := by
  intro σ' σ hR hT
  obtain ⟨hA, he0, ha⟩ := hR
  have he' : σ' e = [] := by
    cases hev : σ' e with
    | nil => rfl
    | cons v vs => have := hT le; rw [step_graph P.he', fire_fork hev] at this; cases this
  have heq : σ' = σ := by
    funext c
    by_cases h1 : c = e
    · subst h1; rw [he', he0]
    · by_cases h2 : c ∈ a
      · rw [ha c h2, he', List.append_nil]
      · exact hA c (fun h => by rcases List.mem_cons.mp h with h | h; exact h1 h; exact h2 h)
  subst heq
  refine ⟨σ', 0, Run.refl _, ?_, fun _ _ => rfl⟩
  intro l
  by_cases e1 : l = lf
  · have hx0 : σ' x = [] := by
      cases hxv : σ' x with
      | nil => rfl
      | cons v vs => have := hT lf; rw [step_graph P.hf', fire_fork hxv] at this; cases this
    rw [e1, step_graph P.hf, fire_fork_none hx0]; rfl
  · by_cases e2 : l = le
    · rw [e2]; exact none_none P.he σ'
    · have := hT l; rw [← this]
      cases hr : rs[l]? with
      | none => rw [none_none hr, none_none (by rw [P.hsame l e1 e2]; exact hr)]
      | some r => rw [step_graph hr, step_graph (by rw [P.hsame l e1 e2]; exact hr)]

theorem fs_forward (P : PatFS rs rs' lf le x e a b) {σ0 t : Store Nat Nat} {n : Nat}
    (h0 : σ0 e = []) (hr : Run (step (graph rs)) σ0 n t) (ht : Terminal (step (graph rs)) t) :
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧ Agree [e] t t' :=
  sim_complete (RelFS e a) (Agree [e]) (fs_fwd_step P) (fs_fwd_term P) hr ht σ0 (relFS_refl h0)

theorem fs_backward (P : PatFS rs rs' lf le x e a b) {σ0 t' : Store Nat Nat} {n : Nat}
    (h0 : σ0 e = []) (hr : Run (step (graph rs')) σ0 n t') (ht : Terminal (step (graph rs')) t') :
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧ Agree [e] t' t :=
  sim_complete (fun σ' σ => RelFS e a σ σ') (Agree [e])
    (fun σ' σ l u' hR hs => fs_bwd_step P σ' σ l u' hR hs) (fun σ' σ hR hT => fs_bwd_term P σ' σ hR hT)
    hr ht σ0 (relFS_refl h0)

end FS

end Formal.Rewrite.Steps
