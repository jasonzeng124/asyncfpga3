import Formal.Rewrite.Steps.JoinExt

/-!
# Formal.Rewrite.Steps.JoinExtSim — a loop update may also wait for the loop bound (shard A, 2026-11-19)

**Problem, plainly.** research's `BDC_RING_FUSE` (on under `BDC_AUTO=1`, flow v8) merges a loop's update `u = F(x)` and
its test `c = G(x, n)` into one cell, whose single join waits for `x` AND `n`. Once the packed cell is unpacked, the
fused graph differs from the unfused one in one rule: the update waits for its own copy `n2` of `n`:

  unfused:  fork n ns ;        comp [x2] u F
  fused:    fork n (n2 :: ns) ; comp [x2, n2] u F'      (F' [x, w] = F [x])

Does the extra wait change anything, whatever surrounds it? It cannot make anything new happen; can it deadlock? Not
when the reader of `u` is a branch steered by a copy of `c` (research's shape: `steer(c, u)`): the k-th `u` is
consumed only together with the k-th `c`, which already needed the k-th `n`.

**Proved** (`je_forward`, `je_backward`): for ANY imported graph `rs` holding `fork x xs` (`x1, x2 ∈ xs`),
`fork n ns` (`n1 ∈ ns`), `comp [x1, n1] c G`, `fork c cs` (`cc ∈ cs`), `branch cc u t f` and `comp [x2] u F`, where no
other rule reads or writes `x1 x2 n1 n2 c cc u` (`PatJE`), and `rs'` equal except `fork n (n2 :: ns)` and
`comp [x2, n2] u F'` with `F' [v, w] = F [v]`: from any store with those seven channels empty, every complete run of
either graph is matched by a complete run of the other ending in the same store outside `x2 n2 u`.

**How.** `InvJ` (`JoinExt`): in `rs'`, `|x2| + |u| = |x1| + |c| + |cc|` and `|n2| + |u| = |n1| + |c| + |cc|`. Forward,
`rs` runs ahead of `rs'` by a list `D` of `x` values it has already turned into `u`; when `rs` fires the branch on a
`u` that `rs'` lacks, the condition token on `cc` and `InvJ` give `rs'` a token on `x2` and on `n2`, so it fires its
update first. Backward, `rs` copies `rs'` step by step; at the end it drains its update, and `InvJ` shows a terminal
`rs'` has no condition token waiting on an empty `u`, so the drained `rs` is terminal too.

**Not covered:** token level only; that bdc's packed cell unpacks to this shape (the planner's job, checked per kernel);
a reader of `u` other than one branch.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

section JES

variable {rs rs' : List Rule} {lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f : Nat} {xs ns cs : List Nat}
  {G F F' : E}

/-! ## Forward: `rs` runs ahead of `rs'` by the list `D` -/

def RelJF (x1 x2 n1 n2 c cc u : Nat) (F : E) (σ σ' : Store Nat Nat) : Prop :=
  Agree [x2, n2, u] σ σ' ∧ InvJ x1 x2 n1 n2 c cc u σ' ∧
  ∃ D : List Nat, σ' x2 = D ++ σ x2 ∧ σ u = σ' u ++ D.map (fun v => F.eval [v])

/-- One firing of the update in `rs'`, consuming the front `d` of `x2` and a token of `n2`. -/
theorem je_fire_u (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F')
    {σ' : Store Nat Nat} {d w : Nat} {ds ws : List Nat} (hx : σ' x2 = d :: ds) (hn : σ' n2 = w :: ws) :
    step (graph rs') σ' lu = some (applyF σ' (popOf [x2, n2], fun ch => if ch = u then [F.eval [d]] else [])) ∧
    ∀ ch, applyF σ' (popOf [x2, n2], fun ch => if ch = u then [F.eval [d]] else []) ch =
      if ch = x2 then ds else if ch = n2 then ws else if ch = u then σ' u ++ [F.eval [d]] else σ' ch := by
  jdist P
  have hall : ∀ ch ∈ [x2, n2], σ' ch ≠ [] := by
    intro ch hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [hx]; exact List.cons_ne_nil _ _
    · rw [hn]; exact List.cons_ne_nil _ _
  have hv : F'.eval ([x2, n2].map (hd σ')) = F.eval [d] := by
    simp only [List.map_cons, List.map_nil, hd, hx, hn, List.headD_cons]; exact P.hF d w
  have ho : u ∉ [x2, n2] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
  refine ⟨?_, fun ch => ?_⟩
  · rw [step_of_fire P.hu' (fire_comp hall), hv]
  · rw [comp_atv ho]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    by_cases e1 : ch = x2
    · subst e1; simp [hx]
    · by_cases e2 : ch = n2
      · subst e2; simp [e1, hn]
      · by_cases e3 : ch = u
        · subst e3; simp [e1, e2]
        · simp [e1, e2, e3]

theorem je_fwd_step (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F') :
    ∀ σ σ' l σ1, RelJF x1 x2 n1 n2 c cc u F σ σ' → step (graph rs) σ l = some σ1 →
      ∃ σ1' k, Run (step (graph rs')) σ' k σ1' ∧ RelJF x1 x2 n1 n2 c cc u F σ1 σ1' := by
  intro σ σ' l σ1 ⟨hA, hI, D, hx2, hu⟩ hs
  jdist P; have T := P.tf
  by_cases e2 : l = lu
  · subst e2
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.hu hs
    obtain ⟨hall, rfl⟩ := comp_inv hf
    obtain ⟨v, vs, hv⟩ := cons_of_ne (hall x2 (by simp))
    have ho : u ∉ [x2] := by simp only [List.mem_singleton]; nd
    refine ⟨σ', 0, Run.refl _, ?_, hI, D ++ [v], ?_, ?_⟩
    · intro ch hch
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hch
      rw [comp_atv ho]; simp only [List.mem_singleton, hch.1, hch.2.2, ite_false]
      exact hA ch (by simp [hch.1, hch.2.1, hch.2.2])
    · rw [comp_atv ho, hx2, hv]; simp
    · rw [comp_atv ho, hu]; simp [show u ≠ x2 by nd, hd, hv]
  by_cases e3 : l = lb
  · subst e3
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.hb hs
    obtain ⟨b, bs, y, ys, hb, hy, rfl⟩ := branch_inv hf
    have hcc' : σ' cc = b :: bs := by
      rw [hA cc (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd, by nd⟩)]
      exact hb
    have bx2 := brOut_nil (b := b) (y := y) T.2.1 T.2.2.2.2.2.2.2.2.1
    have bu := brOut_nil (b := b) (y := y) T.2.2.2.2.2.2.1 T.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hcu : cc ≠ u := by nd
    cases hu' : σ' u with
    | cons y' ys' =>
      rw [hu', hy, List.cons_append] at hu
      injection hu with e1 e2; subst e1
      have hs' := step_of_fire P.rb' (branch_some (t := t) (f := f) hcc' hu')
      refine ⟨_, 1, run_one hs', applyF_agree hA _, invJ_step P hI hs', D, ?_, ?_⟩
      · simp only [branch_at hcu, bx2, hx2]; simp [show x2 ≠ cc by nd, show x2 ≠ u by nd]
      · simp only [branch_at hcu, bu, hy, hu']; simp [e2]
    | nil =>
      rw [hu', List.nil_append, hy] at hu
      cases D with
      | nil => cases hu
      | cons d D' =>
        simp only [List.map_cons] at hu
        injection hu with e1 e2
        obtain ⟨w, ws, hn⟩ : ∃ w ws, σ' n2 = w :: ws := by
          apply cons_of_ne; apply ne_of_len
          have := hI.2; rw [hu', hcc'] at this; simp only [List.length_cons, List.length_nil] at this; omega
        obtain ⟨hs1, hσ2⟩ := je_fire_u P (hx2.trans (List.cons_append ..)) hn
        generalize applyF σ' (popOf [x2, n2], fun ch => if ch = u then [F.eval [d]] else []) = S at hs1 hσ2
        have h2cc : S cc = b :: bs := by
          rw [hσ2]; simp [show cc ≠ x2 by nd, show cc ≠ n2 by nd, hcu, hcc']
        have h2u : S u = y :: [] := by
          rw [hσ2]; simp [show u ≠ x2 by nd, show u ≠ n2 by nd, hu', e1]
        have hs2 := step_of_fire P.rb' (branch_some (t := t) (f := f) h2cc h2u)
        refine ⟨_, 2, Run.cons lu hs1 (run_one hs2), ?_, invJ_step P (invJ_step P hI hs1) hs2, D', ?_, ?_⟩
        · intro ch hch
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hch
          simp only [applyF_at, hσ2 ch]; simp only [hch.1, hch.2.1, hch.2.2, ite_false]
          rw [hA ch (by simp [hch.1, hch.2.1, hch.2.2])]
        · simp only [branch_at hcu, bx2, hσ2]; simp [show x2 ≠ cc by nd, show x2 ≠ u by nd]
        · simp only [branch_at hcu, bu, hy, h2u]; simp [e2]
  by_cases e1 : l = ln
  · subst e1
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.hn hs
    obtain ⟨v, vs, hv, rfl⟩ := fork_inv hf
    have hv' : σ' n = v :: vs := by
      rw [hA n (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd, by nd⟩)]
      exact hv
    have hs' := step_of_fire P.hn' (fire_fork (os := n2 :: ns) hv')
    have hi : n ∉ ns := P.hns.2.1
    have hi' : n ∉ n2 :: ns := by simp only [List.mem_cons, not_or]; exact ⟨by nd, hi⟩
    have hns := P.hns
    refine ⟨_, 1, run_one hs', ?_, invJ_step P hI hs', D, ?_, ?_⟩
    · intro ch hch
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hch
      rw [fork_at hi, fork_at hi']
      by_cases e : ch = n
      · subst e; simp [hv, hv']
      · simp only [e, ite_false, List.mem_cons, hch.2.1, false_or]
        rw [hA ch (by simp [hch.1, hch.2.1, hch.2.2])]
    · rw [fork_at hi, fork_at hi']; simp [show x2 ≠ n by nd, show x2 ≠ n2 by nd, hns.2.2.2.1, hx2]
    · rw [fork_at hi, fork_at hi']; simp [show u ≠ n by nd, show u ≠ n2 by nd, hns.2.2.2.2.2.2.2, hu]
  -- any other label: the same rule on both sides
  cases hr : rs[l]? with
  | none => rw [step_graph_none hr] at hs; cases hs
  | some r =>
    have hr' : rs'[l]? = some r := by rw [P.hsame l e1 e2]; exact hr
    obtain ⟨hrd, huo⟩ := P.other e1 e3 e2 hr
    obtain ⟨fr, hf, rfl, hs'⟩ := outside_step hr hr' hrd hA hs
    have hf' : r.fire natVI σ' = some fr := by rw [fire_agree hA r hrd]; exact hf
    refine ⟨_, 1, run_one hs', applyF_agree hA fr, invJ_step P hI hs', D, ?_, ?_⟩
    · rw [applyF_app hf (nin_of hrd (by simp)), applyF_app hf' (nin_of hrd (by simp)), hx2, List.append_assoc]
    · rw [applyF_app hf (nin_of hrd (by simp)), applyF_app hf' (nin_of hrd (by simp)), fire_push0 hf huo, hu]
      simp

/-- `rs'` fires its update until `x2` or `n2` is empty; `rs` (terminal, so `x2` empty there) stays related. -/
theorem je_drain (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F')
    {σ : Store Nat Nat} (hx : σ x2 = []) :
    ∀ (D : List Nat) (σ' : Store Nat Nat), Agree [x2, n2, u] σ σ' → InvJ x1 x2 n1 n2 c cc u σ' →
      σ' x2 = D ++ σ x2 → σ u = σ' u ++ D.map (fun v => F.eval [v]) →
      ∃ t' m, Run (step (graph rs')) σ' m t' ∧ RelJF x1 x2 n1 n2 c cc u F σ t' ∧ (t' x2 = [] ∨ t' n2 = []) := by
  jdist P
  intro D
  induction D with
  | nil =>
    intro σ' hA hI hx2 hu
    exact ⟨σ', 0, Run.refl _, ⟨hA, hI, [], hx2, hu⟩, Or.inl (by rw [hx2, hx]; rfl)⟩
  | cons d D' ih =>
    intro σ' hA hI hx2 hu
    cases hn : σ' n2 with
    | nil => exact ⟨σ', 0, Run.refl _, ⟨hA, hI, d :: D', hx2, hu⟩, Or.inr hn⟩
    | cons w ws =>
      obtain ⟨hs1, hσ2⟩ := je_fire_u P (hx2.trans (List.cons_append ..)) hn
      generalize applyF σ' (popOf [x2, n2], fun ch => if ch = u then [F.eval [d]] else []) = S at hs1 hσ2
      have hA2 : Agree [x2, n2, u] σ S := by
        intro ch hch
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hch
        rw [hσ2]; simp only [hch.1, hch.2.1, hch.2.2, ite_false]; exact hA ch (by simp [hch.1, hch.2.1, hch.2.2])
      have hx2' : S x2 = D' ++ σ x2 := by rw [hσ2]; simp
      have hu2 : σ u = S u ++ D'.map (fun v => F.eval [v]) := by
        rw [hσ2]; simp [show u ≠ x2 by nd, show u ≠ n2 by nd, hu]
      obtain ⟨t', m, hr, hR, hend⟩ := ih S hA2 (invJ_step P hI hs1) hx2' hu2
      exact ⟨t', m + 1, Run.cons lu hs1 hr, hR, hend⟩

theorem je_fwd_term (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F') :
    ∀ σ σ', RelJF x1 x2 n1 n2 c cc u F σ σ' → Terminal (step (graph rs)) σ →
      ∃ t' m, Run (step (graph rs')) σ' m t' ∧ Terminal (step (graph rs')) t' ∧ Agree [x2, n2, u] σ t' := by
  intro σ σ' ⟨hA, hI, D, hx2, hu⟩ ht
  jdist P
  have hx : σ x2 = [] := by
    have h := step_none_inv P.hu (ht lu)
    cases hv : σ x2 with
    | nil => rfl
    | cons v vs =>
    have hall : ∀ ch ∈ [x2], σ ch ≠ [] := by
      intro ch hc; simp only [List.mem_singleton] at hc; subst hc; rw [hv]; exact List.cons_ne_nil _ _
    rw [fire_comp hall] at h; cases h
  obtain ⟨t', m, hr, ⟨hA', hI', D', hx2', hu'⟩, hend⟩ := je_drain P hx D σ' hA hI hx2 hu
  refine ⟨t', m, hr, fun l => ?_, hA'⟩
  have nchg : ∀ ch, ch ≠ x2 → ch ≠ n2 → ch ≠ u → t' ch = σ ch := fun ch h1 h2 h3 =>
    hA' ch (by simp [h1, h2, h3])
  by_cases e2 : l = lu
  · subst e2; apply step_none_of P.hu'
    rcases hend with h | h
    · exact fire_comp_none (by simp) h
    · exact fire_comp_none (by simp) h
  by_cases e3 : l = lb
  · subst e3; apply step_none_of P.rb'; apply branch_none
    rcases branch_none_inv (step_none_inv P.hb (ht _)) with h | h
    · left; rw [nchg cc (by nd) (by nd) (by nd)]; exact h
    · right; rw [h] at hu'; exact (List.append_eq_nil_iff.mp hu'.symm).1
  by_cases e1 : l = ln
  · subst e1; apply step_none_of P.hn'; apply fire_fork_none
    rw [nchg n (by nd) (by nd) (by nd)]; exact fork_none_inv (step_none_inv P.hn (ht _))
  cases hr : rs[l]? with
  | none => exact step_graph_none (by rw [P.hsame l e1 e2]; exact hr) t'
  | some r =>
    have hr' : rs'[l]? = some r := by rw [P.hsame l e1 e2]; exact hr
    exact outside_none hr hr' (P.other e1 e3 e2 hr).1 hA' (ht l)

theorem je_forward (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F')
    {σ0 t : Store Nat Nat} {k : Nat} (h0 : ∀ ch ∈ [x1, x2, n1, n2, c, cc, u], σ0 ch = [])
    (hr : Run (step (graph rs)) σ0 k t) (ht : Terminal (step (graph rs)) t) :
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧ Agree [x2, n2, u] t t' := by
  have hI : InvJ x1 x2 n1 n2 c cc u σ0 := by
    unfold InvJ
    rw [h0 x1 (by simp), h0 x2 (by simp), h0 n1 (by simp), h0 n2 (by simp), h0 c (by simp), h0 cc (by simp),
      h0 u (by simp)]
    exact ⟨rfl, rfl⟩
  exact sim_complete (RelJF x1 x2 n1 n2 c cc u F) (Agree [x2, n2, u]) (je_fwd_step P) (je_fwd_term P) hr ht σ0
    ⟨fun _ _ => rfl, hI, [], rfl, by simp⟩

/-! ## Backward: `rs` copies `rs'`, then drains its update -/

def RelJB (x1 x2 n1 n2 c cc u : Nat) (σ' σ : Store Nat Nat) : Prop :=
  Agree [n2] σ' σ ∧ InvJ x1 x2 n1 n2 c cc u σ'

theorem je_bwd_step (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F') :
    ∀ σ' σ l σ1', RelJB x1 x2 n1 n2 c cc u σ' σ → step (graph rs') σ' l = some σ1' →
      ∃ σ1 k, Run (step (graph rs)) σ k σ1 ∧ RelJB x1 x2 n1 n2 c cc u σ1' σ1 := by
  intro σ' σ l σ1' ⟨hA, hI⟩ hs
  jdist P
  have hI1 := invJ_step P hI hs
  by_cases e2 : l = lu
  · subst e2
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.hu' hs
    obtain ⟨hall, rfl⟩ := comp_inv hf
    obtain ⟨d, ds, hd'⟩ := cons_of_ne (hall x2 (by simp))
    obtain ⟨w, ws, hn'⟩ := cons_of_ne (hall n2 (by simp))
    have hdx : σ x2 = d :: ds := by rw [hA x2 (by simp only [List.mem_singleton]; nd)]; exact hd'
    have hall1 : ∀ ch ∈ [x2], σ ch ≠ [] := by
      intro ch hc; simp only [List.mem_singleton] at hc; subst hc; rw [hdx]; exact List.cons_ne_nil _ _
    have hs1 := step_of_fire P.hu (fire_comp hall1)
    refine ⟨_, 1, run_one hs1, fun ch hch => ?_, hI1⟩
    simp only [List.mem_singleton] at hch
    have ho : u ∉ [x2, n2] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
    have ho1 : u ∉ [x2] := by simp only [List.mem_singleton]; nd
    rw [comp_atv ho, comp_atv ho1]
    simp only [List.mem_cons, List.not_mem_nil, or_false, hch]
    by_cases ex : ch = x2
    · subst ex; simp [hd', hdx]
    · by_cases eu : ch = u
      · subst eu
        simp only [ex, ite_true, ite_false, List.map_cons, List.map_nil, hd, hd', hdx, hn', List.headD_cons]
        rw [P.hF d w, hA ch (by simp only [List.mem_singleton]; nd)]
      · simp only [ex, eu, ite_false]; exact hA ch (by simp only [List.mem_singleton]; exact hch)
  by_cases e1 : l = ln
  · subst e1
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.hn' hs
    obtain ⟨v, vs, hv', rfl⟩ := fork_inv hf
    have hv : σ n = v :: vs := by rw [hA n (by simp only [List.mem_singleton]; nd)]; exact hv'
    have hs1 := step_of_fire P.hn (fire_fork (os := ns) hv)
    have hi : n ∉ ns := P.hns.2.1
    have hi' : n ∉ n2 :: ns := by simp only [List.mem_cons, not_or]; exact ⟨by nd, hi⟩
    refine ⟨_, 1, run_one hs1, fun ch hch => ?_, hI1⟩
    simp only [List.mem_singleton] at hch
    rw [fork_at hi, fork_at hi']
    by_cases e : ch = n
    · subst e; simp [hv, hv']
    · simp only [e, ite_false, List.mem_cons, hch, false_or]
      rw [hA ch (by simp only [List.mem_singleton]; exact hch)]
  -- any other label: the same rule on both sides, reading no `n2`
  cases hr : rs[l]? with
  | none => rw [step_graph_none (by rw [P.hsame l e1 e2]; exact hr)] at hs; cases hs
  | some r =>
    have hr' : rs'[l]? = some r := by rw [P.hsame l e1 e2]; exact hr
    obtain ⟨fr, -, rfl, hs1⟩ := outside_step hr' hr (P.reads_n2 e1 e2 hr) hA hs
    exact ⟨_, 1, run_one hs1, applyF_agree hA fr, hI1⟩

theorem je_bwd_term (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F') :
    ∀ σ' σ, RelJB x1 x2 n1 n2 c cc u σ' σ → Terminal (step (graph rs')) σ' →
      ∃ t m, Run (step (graph rs)) σ m t ∧ Terminal (step (graph rs)) t ∧ Agree [x2, n2, u] σ' t := by
  intro σ' σ ⟨hA, hI⟩ ht
  jdist P
  obtain ⟨m, hr⟩ := drain_comp1f P.hu (show x2 ≠ u by nd) (σ x2) σ rfl
  generalize hτ : (fun ch => if ch = x2 then [] else if ch = u then σ u ++ (σ x2).map (fun v => F.eval [v])
    else σ ch) = τ at hr
  have hτx : τ x2 = [] := by rw [← hτ]; simp
  have hτo : ∀ ch, ch ≠ x2 → ch ≠ u → τ ch = σ ch := by
    intro ch h1 h2; rw [← hτ]; simp [h1, h2]
  have hA' : Agree [x2, n2, u] σ' τ := by
    intro ch hch
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hch
    rw [hτo ch hch.1 hch.2.2]; exact hA ch (by simp only [List.mem_singleton]; exact hch.2.1)
  refine ⟨τ, m, hr, fun l => ?_, hA'⟩
  by_cases e2 : l = lu
  · subst e2; exact step_none_of P.hu (fire_comp_none (by simp) hτx)
  by_cases e3 : l = lb
  · subst e3; apply step_none_of P.hb; apply branch_none; left
    have hcc : σ' cc = [] := by
      apply Classical.byContradiction; intro hne
      rcases branch_none_inv (step_none_inv P.rb' (ht _)) with h | h
      · exact hne h
      · -- a condition token waits on an empty `u`: by `InvJ`, `rs'` could fire its update
        have l1 : (σ' x2).length ≠ 0 := by
          have := hI.1; rw [h] at this; simp only [List.length_nil] at this
          have : (σ' cc).length ≠ 0 := fun e => hne (List.eq_nil_of_length_eq_zero e)
          omega
        have l2 : (σ' n2).length ≠ 0 := by
          have := hI.2; rw [h] at this; simp only [List.length_nil] at this
          have : (σ' cc).length ≠ 0 := fun e => hne (List.eq_nil_of_length_eq_zero e)
          omega
        have hall : ∀ ch ∈ [x2, n2], σ' ch ≠ [] := by
          intro ch hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact ne_of_len l1
          · exact ne_of_len l2
        have := ht lu
        rw [step_of_fire P.hu' (fire_comp hall)] at this; cases this
    rw [hτo cc (by nd) (by nd), hA cc (by simp only [List.mem_singleton]; nd)]; exact hcc
  by_cases e1 : l = ln
  · subst e1; apply step_none_of P.hn; apply fire_fork_none
    rw [hτo n (by nd) (by nd), hA n (by simp only [List.mem_singleton]; nd)]
    exact fork_none_inv (step_none_inv P.hn' (ht _))
  cases hr : rs[l]? with
  | none => exact step_graph_none hr τ
  | some r =>
    have hr' : rs'[l]? = some r := by rw [P.hsame l e1 e2]; exact hr
    exact outside_none hr' hr (P.other e1 e3 e2 hr).1 hA' (ht l)

theorem je_backward (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F')
    {σ0 t' : Store Nat Nat} {k : Nat} (h0 : ∀ ch ∈ [x1, x2, n1, n2, c, cc, u], σ0 ch = [])
    (hr : Run (step (graph rs')) σ0 k t') (ht : Terminal (step (graph rs')) t') :
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧ Agree [x2, n2, u] t' t := by
  have hI : InvJ x1 x2 n1 n2 c cc u σ0 := by
    unfold InvJ
    rw [h0 x1 (by simp), h0 x2 (by simp), h0 n1 (by simp), h0 n2 (by simp), h0 c (by simp), h0 cc (by simp),
      h0 u (by simp)]
    exact ⟨rfl, rfl⟩
  exact sim_complete (RelJB x1 x2 n1 n2 c cc u) (fun σ' τ => Agree [x2, n2, u] σ' τ) (je_bwd_step P)
    (je_bwd_term P) hr ht σ0 ⟨fun _ _ => rfl, hI⟩

end JES

end Formal.Rewrite.Steps
