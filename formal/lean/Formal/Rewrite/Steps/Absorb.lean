import Formal.Rewrite.Steps.Basic

/-!
# Formal.Rewrite.Steps.Absorb — a comp folded into its only reader (shard A, 2026-11-19)

**Problem, plainly.** A comp computes `p = f(a1, ..., ak)` and the only rule that reads `p` is a comp
`q = g(b1, ..., bm, p)`. Is that the same, whatever surrounds it, as the single comp
`q = g(b1, ..., bm, f(a1, ..., ak))` reading `b1 .. bm, a1 .. ak`? This is operator fusion (bdc's region fusion,
research's ringfuse) and the building block of the pass that moves a loop test (pre_eq2).

**Proved** (`ab_forward`, `ab_backward`): for ANY imported graph `rs` holding `comp as p f` at `lp` and
`comp (bs ++ [p]) q g` at `lq`, and `rs'` equal except the dead rule `sink p` at `lp` and
`comp (bs ++ as) q (absorbE |bs| |as| f g)` at `lq` (`absorbE` substitutes `f` for `g`'s last input), with
`p :: bs ++ as` distinct, `q` not among them, `as` non-empty, no other rule reading `p` or the `ai`, and no other rule
writing `p`: from any store with `p` empty, every complete run of either graph is matched by a complete run of the
other ending in the same store outside `p` and the `ai`.

**Not covered:** token level only.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

/-! ## The fused expression -/

def absorbE (nb na : Nat) (f g : E) : E :=
  g.subst ((List.range nb).map E.var ++ [f.subst ((List.range na).map (fun j => E.var (nb + j)))])

theorem range_getD (l : List Nat) : (List.range l.length).map (fun i => l.getD i 0) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem eval_absorbE (f g : E) (vb va : List Nat) :
    (absorbE vb.length va.length f g).eval (vb ++ va) = g.eval (vb ++ [f.eval va]) := by
  have hb : (List.range vb.length).map (fun i => (E.var i).eval (vb ++ va)) = vb := by
    conv => rhs; rw [← range_getD vb]
    apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
    simp [E.eval, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have ha : (List.range va.length).map (fun j => (E.var (vb.length + j)).eval (vb ++ va)) = va := by
    conv => rhs; rw [← range_getD va]
    apply List.map_congr_left; intro j _
    simp [E.eval, List.getD_eq_getElem?_getD, List.getElem?_append_right]
  unfold absorbE
  rw [eval_subst, List.map_append, List.map_map, List.map_cons, List.map_nil, eval_subst, List.map_map]
  simp only [Function.comp_def]
  rw [hb, ha]

/-- Reading a tuple back through positions. -/
theorem map_getD_eq (as t : List Nat) (h : t.length = as.length) :
    (List.range as.length).map (fun j => t.getD j 0) = t := by
  rw [← h]; exact range_getD t

/-- A channel of `as`, given by its position. -/
theorem mem_pos {as : List Nat} {c : Nat} (h : c ∈ as) : ∃ j, ∃ hj : j < as.length, as[j] = c :=
  List.getElem_of_mem h

/-- From the positional relation: the heads of `as` in `σ'` are the first tuple. -/
theorem heads_tuple {as : List Nat} {σ σ' : Store Nat Nat} {t0 : List Nat} {Lt : List (List Nat)}
    (hl : t0.length = as.length)
    (has : ∀ j (hj : j < as.length), σ' as[j] = (t0 :: Lt).map (fun t => t.getD j 0) ++ σ as[j]) :
    as.map (hd σ') = t0 := by
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  simp only [List.getElem_map]
  have := has j (by simpa using h1)
  simp only [hd, this, List.map_cons, List.cons_append, List.headD_cons]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-! ## Draining a comp until one input is empty -/

theorem drain_comp {rs : List Rule} {l o c0 : Nat} {cr : List Nat} {F : E}
    (hr : rs[l]? = some (.comp (c0 :: cr) o F)) (ho : o ∉ c0 :: cr) :
    ∀ k (σ : Store Nat Nat), (σ c0).length = k →
      ∃ τ n, Run (step (graph rs)) σ n τ ∧ (∃ c ∈ c0 :: cr, τ c = []) ∧ Agree (o :: c0 :: cr) σ τ := by
  intro k
  induction k with
  | zero =>
    intro σ hk
    exact ⟨σ, 0, Run.refl _, ⟨c0, List.mem_cons_self, List.length_eq_zero_iff.mp hk⟩, fun _ _ => rfl⟩
  | succ k ih =>
    intro σ hk
    by_cases hall : ∀ c ∈ c0 :: cr, σ c ≠ []
    · have hs : step (graph rs) σ l = some (applyF σ (popOf (c0 :: cr),
          fun c => if c = o then [F.eval ((c0 :: cr).map (hd σ))] else [])) := by
        rw [step_graph hr, fire_comp hall]; rfl
      obtain ⟨τ, n, hrun, hemp, hA⟩ := ih (applyF σ (popOf (c0 :: cr),
          fun c => if c = o then [F.eval ((c0 :: cr).map (hd σ))] else [])) (by
        rw [comp_at ho]; simp [hk])
      refine ⟨τ, n + 1, Run.cons l hs hrun, hemp, ?_⟩
      intro c hc
      rw [hA c hc, comp_at ho]
      have h1 : c ≠ o := fun e => hc (by simp [e])
      have h2 : c ∉ c0 :: cr := fun h => hc (List.mem_cons_of_mem _ h)
      simp [h1, h2]
    · obtain ⟨c, hc, he⟩ := exists_empty hall
      exact ⟨σ, 0, Run.refl _, ⟨c, hc, he⟩, fun _ _ => rfl⟩

/-! ## The pattern -/

structure PatAB (rs rs' : List Rule) (lp lq p q a0 : Nat) (ar bs : List Nat) (f g : E) : Prop where
  hp : rs[lp]? = some (.comp (a0 :: ar) p f)
  hq : rs[lq]? = some (.comp (bs ++ [p]) q g)
  hp' : rs'[lp]? = some (.sink p)
  hq' : rs'[lq]? = some (.comp (bs ++ a0 :: ar) q (absorbE bs.length (a0 :: ar).length f g))
  hlpq : lp ≠ lq
  hsame : ∀ l, l ≠ lp → l ≠ lq → rs'[l]? = rs[l]?
  hins : ∀ l r, l ≠ lp → l ≠ lq → rs[l]? = some r → ∀ c ∈ r.insL, c ∉ p :: a0 :: ar
  houts : ∀ l r, l ≠ lp → rs[l]? = some r → p ∉ r.outsL
  hnd : (p :: (bs ++ a0 :: ar)).Nodup
  hqn : q ∉ p :: (bs ++ a0 :: ar)

section AB
variable {rs rs' : List Rule} {lp lq p q a0 : Nat} {ar bs : List Nat} {f g : E}

/-- `Lt`: the argument tuples `f` has consumed in `rs` whose results the reader has not yet consumed; in `rs'` they
are still on the `ai`. -/
def RelAB (p : Nat) (as : List Nat) (f : E) (σ σ' : Store Nat Nat) : Prop :=
  ∃ Lt : List (List Nat), (∀ t ∈ Lt, t.length = as.length) ∧ Agree (p :: as) σ σ' ∧
    σ p = Lt.map f.eval ∧ σ' p = [] ∧ ∀ j (hj : j < as.length), σ' as[j] = Lt.map (fun t => t.getD j 0) ++ σ as[j]

section Facts
variable (P : PatAB rs rs' lp lq p q a0 ar bs f g)
include P

theorem PatAB.p_nin_as : p ∉ a0 :: ar := by
  have := P.hnd; simp only [List.nodup_cons, List.mem_append, not_or] at this; exact this.1.2
theorem PatAB.p_nin_bs : p ∉ bs := by
  have := P.hnd; simp only [List.nodup_cons, List.mem_append, not_or] at this; exact this.1.1
theorem PatAB.as_nd : (a0 :: ar).Nodup := by
  have := P.hnd; simp only [List.nodup_cons, List.nodup_append] at this ⊢; exact this.2.2.1
theorem PatAB.bs_as {c : Nat} (h : c ∈ bs) : c ∉ a0 :: ar := by
  have := P.hnd; simp only [List.nodup_cons, List.nodup_append] at this
  exact fun h' => this.2.2.2 c h c h' rfl
theorem PatAB.q_nin_bsp : q ∉ bs ++ [p] := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact P.hqn (List.mem_cons_of_mem _ (List.mem_append_left _ h))
  · exact P.hqn (by simp at h; simp [h])
theorem PatAB.q_nin_bsa : q ∉ bs ++ a0 :: ar := fun h => P.hqn (List.mem_cons_of_mem _ h)
theorem PatAB.q_ne_p : q ≠ p := fun h => P.hqn (by simp [h])
theorem PatAB.p_nin_q : p ∉ (a0 :: ar) := P.p_nin_as

end Facts

theorem PatAB.out (P : PatAB rs rs' lp lq p q a0 ar bs f g) {l : Nat} {r : Rule} (h1 : l ≠ lp) (h2 : l ≠ lq)
    (hr : rs[l]? = some r) : rs'[l]? = some r ∧ ∀ c ∈ r.insL, c ∉ p :: a0 :: ar :=
  ⟨by rw [P.hsame l h1 h2, hr], P.hins l r h1 h2 hr⟩

/-- In both graphs the reader's `bs` heads agree (the stores agree there). -/
theorem bs_heads {σ σ' : Store Nat Nat} (P : PatAB rs rs' lp lq p q a0 ar bs f g)
    (hA : Agree (p :: a0 :: ar) σ σ') : bs.map (hd σ') = bs.map (hd σ) := by
  apply List.map_congr_left; intro c hc
  simp only [hd]; rw [hA c (fun h => by
    rcases List.mem_cons.mp h with h | h
    · exact P.p_nin_bs (h ▸ hc)
    · exact P.bs_as hc h)]

/-- The reader's firing in `rs'` produces the reader's firing in `rs` on the matching tuple. -/
theorem out_match (P : PatAB rs rs' lp lq p q a0 ar bs f g) {σ σ' : Store Nat Nat} {t : List Nat}
    (hA : Agree (p :: a0 :: ar) σ σ') (ht : (a0 :: ar).map (hd σ') = t) (hp : hd σ p = f.eval t) :
    (absorbE bs.length (a0 :: ar).length f g).eval ((bs ++ a0 :: ar).map (hd σ')) =
      g.eval ((bs ++ [p]).map (hd σ)) := by
  have hlt : (a0 :: ar).length = t.length := by rw [← ht, List.length_map]
  have key := eval_absorbE f g (bs.map (hd σ')) t
  simp only [List.length_map] at key
  rw [List.map_append, ht, hlt, key, bs_heads P hA, List.map_append]
  simp [hd] at hp ⊢
  rw [hp]

theorem ab_fwd_step (P : PatAB rs rs' lp lq p q a0 ar bs f g) :
    ∀ σ σ' l u, RelAB p (a0 :: ar) f σ σ' → step (graph rs) σ l = some u →
      ∃ u' n, Run (step (graph rs')) σ' n u' ∧ RelAB p (a0 :: ar) f u u' := by
  intro σ σ' l u ⟨Lt, hLt, hA, hpv, hp', has⟩ hs
  by_cases e1 : l = lp
  · rw [e1, step_graph P.hp] at hs
    by_cases hall : ∀ c ∈ a0 :: ar, σ c ≠ []
    · rw [fire_comp hall] at hs
      have hu := (Option.some.inj hs).symm
      subst hu
      refine ⟨σ', 0, Run.refl _, Lt ++ [(a0 :: ar).map (hd σ)], ?_, ?_, ?_, hp', ?_⟩
      · intro t ht; rcases List.mem_append.mp ht with ht | ht
        · exact hLt t ht
        · simp at ht; subst ht; simp
      · intro c hc
        rw [comp_at P.p_nin_as]
        have h1 : c ∉ a0 :: ar := fun h => hc (List.mem_cons_of_mem _ h)
        have h2 : c ≠ p := fun e => hc (by simp [e])
        simp [h1, h2, hA c hc]
      · rw [comp_at P.p_nin_as, hpv]; simp [P.p_nin_as]
      · intro j hj
        have hc : (a0 :: ar)[j] ∈ a0 :: ar := List.getElem_mem hj
        have hg : ((a0 :: ar).map (hd σ)).getD j 0 = hd σ (a0 :: ar)[j] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
        rw [comp_at P.p_nin_as, has j hj]
        simp only [hc, ite_true, List.map_append, List.append_assoc, List.map_singleton, List.singleton_append]
        rw [hg]
        have hne := hall _ hc
        cases hσ : σ (a0 :: ar)[j] with
        | nil => exact absurd hσ hne
        | cons v vs => simp [hd, hσ]
    · obtain ⟨c, hc, he⟩ := exists_empty hall
      rw [fire_comp_none hc he] at hs; cases hs
  · by_cases e2 : l = lq
    · rw [e2, step_graph P.hq] at hs
      cases Lt with
      | nil =>
        rw [fire_comp_none (List.mem_append_right bs (List.mem_singleton_self p)) (by rw [hpv]; rfl)] at hs
        cases hs
      | cons t0 Lt' =>
        by_cases hall : ∀ c ∈ bs ++ [p], σ c ≠ []
        · rw [fire_comp hall] at hs
          have hu := (Option.some.inj hs).symm
          subst hu
          have hall' : ∀ c ∈ bs ++ a0 :: ar, σ' c ≠ [] := by
            intro c hc
            rcases List.mem_append.mp hc with hc | hc
            · rw [hA c (fun h => by
                rcases List.mem_cons.mp h with h | h
                · exact P.p_nin_bs (h ▸ hc)
                · exact P.bs_as hc h)]
              exact hall c (List.mem_append_left _ hc)
            · obtain ⟨j, hj, rfl⟩ := mem_pos hc; rw [has j hj]; simp
          have ht : (a0 :: ar).map (hd σ') = t0 := heads_tuple (hLt t0 List.mem_cons_self) has
          have hpe : hd σ p = f.eval t0 := by simp [hd, hpv]
          have hs' : step (graph rs') σ' lq = some (applyF σ' (popOf (bs ++ a0 :: ar),
              fun c => if c = q then [(absorbE bs.length (a0 :: ar).length f g).eval
                ((bs ++ a0 :: ar).map (hd σ'))] else [])) := by
            rw [step_graph P.hq', fire_comp hall']; rfl
          refine ⟨_, 1, Run.cons lq hs' (Run.refl _), Lt', fun t ht => hLt t (List.mem_cons_of_mem _ ht),
            ?_, ?_, ?_, ?_⟩
          · intro c hc
            rw [comp_at P.q_nin_bsp, comp_at P.q_nin_bsa, out_match P hA ht hpe]
            have h2 : c ≠ p := fun e => hc (by simp [e])
            have h3 : c ∉ a0 :: ar := fun h => hc (List.mem_cons_of_mem _ h)
            by_cases hb : c ∈ bs
            · simp [hb, hA c hc]
            · simp [hb, h2, h3, hA c hc]
          · rw [comp_at P.q_nin_bsp, hpv]; simp
          · rw [comp_at P.q_nin_bsa]; simp [P.p_nin_bs, P.p_nin_as, hp', P.q_ne_p.symm]
          · intro j hj
            have hc : (a0 :: ar)[j] ∈ a0 :: ar := List.getElem_mem hj
            rw [comp_at P.q_nin_bsa, comp_at P.q_nin_bsp, has j hj]
            have h1 : (a0 :: ar)[j] ∉ bs := fun h => P.bs_as h hc
            have h2 : (a0 :: ar)[j] ≠ p := fun e => P.p_nin_as (e ▸ hc)
            have h4 : (a0 :: ar)[j] ∈ bs ++ a0 :: ar := List.mem_append_right _ hc
            have h5 : (a0 :: ar)[j] ∉ bs ++ [p] := by simp [h1, h2]
            have h6 : (a0 :: ar)[j] ≠ q := fun e => P.q_nin_bsa (e ▸ h4)
            simp only [h4, h5, h6, ite_true, ite_false, List.map_cons, List.cons_append, List.tail_cons]
        · obtain ⟨c, hc, he⟩ := exists_empty hall
          rw [fire_comp_none hc he] at hs; cases hs
    · cases hr : rs[l]? with
      | none => rw [none_none hr] at hs; cases hs
      | some r =>
        obtain ⟨hr', hrd⟩ := P.out e1 e2 hr
        obtain ⟨fr, hf, rfl, hs'⟩ := outside_step hr hr' hrd hA hs
        have hfr' : r.fire natVI σ' = some fr := by rw [fire_agree hA r hrd]; exact hf
        have hpp : fr.2 p = [] := fire_push0 hf (P.houts l r e1 hr)
        refine ⟨_, 1, Run.cons l hs' (Run.refl _), Lt, hLt, applyF_agree hA fr, ?_, ?_, ?_⟩
        · rw [applyF_app hf (nin_of hrd (by simp)), hpp, hpv, List.append_nil]
        · rw [applyF_app hfr' (nin_of hrd (by simp)), hpp, hp', List.append_nil]
        · intro j hj
          have hc : (a0 :: ar)[j] ∈ a0 :: ar := List.getElem_mem hj
          rw [applyF_app hf (nin_of hrd (List.mem_cons_of_mem _ hc)),
            applyF_app hfr' (nin_of hrd (List.mem_cons_of_mem _ hc)), has j hj, List.append_assoc]

theorem ab_fwd_term (P : PatAB rs rs' lp lq p q a0 ar bs f g) :
    ∀ σ σ', RelAB p (a0 :: ar) f σ σ' → Terminal (step (graph rs)) σ →
      ∃ u' n, Run (step (graph rs')) σ' n u' ∧ Terminal (step (graph rs')) u' ∧ Agree (p :: a0 :: ar) σ u' := by
  intro σ σ' ⟨Lt, hLt, hA, hpv, hp', has⟩ hT
  refine ⟨σ', 0, Run.refl _, ?_, hA⟩
  intro l
  by_cases e1 : l = lp
  · rw [e1, step_graph P.hp', fire_sink_none hp']; rfl
  · by_cases e2 : l = lq
    · rw [e2, step_graph P.hq']
      -- the reader is disabled in rs: some b is empty, or p is empty (then Lt = [] and some ai is empty)
      have hq := hT lq
      rw [step_graph P.hq] at hq
      by_cases hall : ∀ c ∈ bs ++ [p], σ c ≠ []
      · rw [fire_comp hall] at hq; cases hq
      · obtain ⟨c, hc, he⟩ := exists_empty hall
        rcases List.mem_append.mp hc with hb | hpc
        · rw [fire_comp_none (List.mem_append_left _ hb) (by
            rw [hA c (fun h => by
              rcases List.mem_cons.mp h with h | h
              · exact P.p_nin_bs (h ▸ hb)
              · exact P.bs_as hb h)]; exact he)]; rfl
        · simp at hpc; subst hpc
          rw [hpv] at he
          have hL : Lt = [] := List.map_eq_nil_iff.mp he
          subst hL
          have hp := hT lp
          rw [step_graph P.hp] at hp
          by_cases hall2 : ∀ c ∈ a0 :: ar, σ c ≠ []
          · rw [fire_comp hall2] at hp; cases hp
          · obtain ⟨d, hd', he2⟩ := exists_empty hall2
            obtain ⟨j, hj, rfl⟩ := mem_pos hd'
            rw [fire_comp_none (List.mem_append_right _ hd') (by rw [has j hj, he2]; rfl)]; rfl
    · cases hr : rs[l]? with
      | none => rw [← P.hsame l e1 e2] at hr; exact none_none hr σ'
      | some r =>
        obtain ⟨hr', hrd⟩ := P.out e1 e2 hr
        exact outside_none hr hr' hrd hA (hT l)

theorem ab_bwd_step (P : PatAB rs rs' lp lq p q a0 ar bs f g) :
    ∀ σ' σ l u', RelAB p (a0 :: ar) f σ σ' → step (graph rs') σ' l = some u' →
      ∃ u n, Run (step (graph rs)) σ n u ∧ RelAB p (a0 :: ar) f u u' := by
  intro σ' σ l u' hR hs
  by_cases e1 : l = lp
  · obtain ⟨_, _, _, _, hp', _⟩ := hR
    rw [e1, step_graph P.hp', fire_sink_none hp'] at hs; cases hs
  · by_cases e2 : l = lq
    · -- if nothing is pending, let f fire first; then the reader fires in both
      have pre : ∃ τ n, Run (step (graph rs)) σ n τ ∧ RelAB p (a0 :: ar) f τ σ' ∧
          ∃ Lt, (∃ t0 Lt', Lt = t0 :: Lt') ∧ (∀ t ∈ Lt, t.length = (a0 :: ar).length) ∧
            Agree (p :: a0 :: ar) τ σ' ∧ τ p = Lt.map f.eval ∧ σ' p = [] ∧
            ∀ j (hj : j < (a0 :: ar).length), σ' (a0 :: ar)[j] = Lt.map (fun t => t.getD j 0) ++ τ (a0 :: ar)[j] := by
        obtain ⟨Lt, hLt, hA, hpv, hp', has⟩ := hR
        rw [e2, step_graph P.hq'] at hs
        by_cases hall' : ∀ c ∈ bs ++ a0 :: ar, σ' c ≠ []
        · cases Lt with
          | cons t0 Lt' =>
            exact ⟨σ, 0, Run.refl _, ⟨_, hLt, hA, hpv, hp', has⟩, _, ⟨t0, Lt', rfl⟩, hLt, hA, hpv, hp', has⟩
          | nil =>
            have hall : ∀ c ∈ a0 :: ar, σ c ≠ [] := fun c hc => by
              have := hall' c (List.mem_append_right _ hc)
              obtain ⟨j, hj, rfl⟩ := mem_pos hc
              rwa [has j hj] at this
            have hs1 : step (graph rs) σ lp = some (applyF σ (popOf (a0 :: ar),
                fun c => if c = p then [f.eval ((a0 :: ar).map (hd σ))] else [])) := by
              rw [step_graph P.hp, fire_comp hall]; rfl
            let τ := applyF σ (popOf (a0 :: ar), fun c => if c = p then [f.eval ((a0 :: ar).map (hd σ))] else [])
            have hAτ : Agree (p :: a0 :: ar) τ σ' := by
              intro c hc
              have h1 : c ∉ a0 :: ar := fun h => hc (List.mem_cons_of_mem _ h)
              have h2 : c ≠ p := fun e => hc (by simp [e])
              simp only [τ, comp_at P.p_nin_as, h1, h2, ite_false]; exact hA c hc
            have hτp : τ p = [(a0 :: ar).map (hd σ)].map f.eval := by
              simp only [τ, comp_at P.p_nin_as, P.p_nin_as, ite_false, ite_true, hpv]; rfl
            have hτa : ∀ j (hj : j < (a0 :: ar).length), σ' (a0 :: ar)[j] =
                [(a0 :: ar).map (hd σ)].map (fun t => t.getD j 0) ++ τ (a0 :: ar)[j] := by
              intro j hj
              have hc : (a0 :: ar)[j] ∈ a0 :: ar := List.getElem_mem hj
              have hg : ((a0 :: ar).map (hd σ)).getD j 0 = hd σ (a0 :: ar)[j] := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
              simp only [τ, comp_at P.p_nin_as, hc, ite_true, has j hj, List.map_nil, List.nil_append]
              rw [List.map_cons, hg, List.map_nil, List.singleton_append]
              cases hσ : σ (a0 :: ar)[j] with
              | nil => exact absurd hσ (hall _ hc)
              | cons v vs => simp [hd, hσ]
            have hLt1 : ∀ t ∈ [(a0 :: ar).map (hd σ)], t.length = (a0 :: ar).length := by simp
            exact ⟨τ, 1, Run.cons lp hs1 (Run.refl _), ⟨_, hLt1, hAτ, hτp, hp', hτa⟩, _, ⟨_, [], rfl⟩, hLt1,
              hAτ, hτp, hp', hτa⟩
        · obtain ⟨c, hc, he⟩ := exists_empty hall'
          rw [fire_comp_none hc he] at hs; cases hs
      obtain ⟨τ, n1, hrun1, -, Lt, ⟨t0, Lt', rfl⟩, hLt, hA, hpv, hp', has⟩ := pre
      rw [e2, step_graph P.hq'] at hs
      by_cases hall' : ∀ c ∈ bs ++ a0 :: ar, σ' c ≠ []
      · rw [fire_comp hall'] at hs
        have hu' := (Option.some.inj hs).symm
        subst hu'
        have hall : ∀ c ∈ bs ++ [p], τ c ≠ [] := by
          intro c hc
          rcases List.mem_append.mp hc with hc | hc
          · have := hall' c (List.mem_append_left _ hc)
            rwa [hA c (fun h => by
              rcases List.mem_cons.mp h with h | h
              · exact P.p_nin_bs (h ▸ hc)
              · exact P.bs_as hc h)] at this
          · simp at hc; subst hc; rw [hpv]; simp
        have ht : (a0 :: ar).map (hd σ') = t0 := heads_tuple (hLt t0 List.mem_cons_self) has
        have hpe : hd τ p = f.eval t0 := by simp [hd, hpv]
        have hs1 : step (graph rs) τ lq = some (applyF τ (popOf (bs ++ [p]),
            fun c => if c = q then [g.eval ((bs ++ [p]).map (hd τ))] else [])) := by
          rw [step_graph P.hq, fire_comp hall]; rfl
        refine ⟨_, n1 + 1, run_trans hrun1 (Run.cons lq hs1 (Run.refl _)), Lt',
          fun t ht => hLt t (List.mem_cons_of_mem _ ht), ?_, ?_, ?_, ?_⟩
        · intro c hc
          rw [comp_at P.q_nin_bsp, comp_at P.q_nin_bsa, out_match P hA ht hpe]
          have h2 : c ≠ p := fun e => hc (by simp [e])
          have h3 : c ∉ a0 :: ar := fun h => hc (List.mem_cons_of_mem _ h)
          by_cases hb : c ∈ bs
          · simp [hb, hA c hc]
          · simp [hb, h2, h3, hA c hc]
        · rw [comp_at P.q_nin_bsp, hpv]; simp
        · rw [comp_at P.q_nin_bsa]; simp [P.p_nin_bs, P.p_nin_as, hp', P.q_ne_p.symm]
        · intro j hj
          have hc : (a0 :: ar)[j] ∈ a0 :: ar := List.getElem_mem hj
          rw [comp_at P.q_nin_bsa, comp_at P.q_nin_bsp, has j hj]
          have h1 : (a0 :: ar)[j] ∉ bs := fun h => P.bs_as h hc
          have h2 : (a0 :: ar)[j] ≠ p := fun e => P.p_nin_as (e ▸ hc)
          have h4 : (a0 :: ar)[j] ∈ bs ++ a0 :: ar := List.mem_append_right _ hc
          have h5 : (a0 :: ar)[j] ∉ bs ++ [p] := by simp [h1, h2]
          have h6 : (a0 :: ar)[j] ≠ q := fun e => P.q_nin_bsa (e ▸ h4)
          simp only [h4, h5, h6, ite_true, ite_false, List.map_cons, List.cons_append, List.tail_cons]
      · obtain ⟨c, hc, he⟩ := exists_empty hall'
        rw [fire_comp_none hc he] at hs; cases hs
    · obtain ⟨Lt, hLt, hA, hpv, hp', has⟩ := hR
      cases hr' : rs'[l]? with
      | none => rw [none_none hr'] at hs; cases hs
      | some r =>
        have hr : rs[l]? = some r := by rw [← P.hsame l e1 e2, hr']
        obtain ⟨-, hrd⟩ := P.out e1 e2 hr
        obtain ⟨fr, hf', rfl, hs2⟩ := outside_step hr' hr hrd hA.symm hs
        have hf : r.fire natVI σ = some fr := by rw [← fire_agree hA r hrd]; exact hf'
        have hpp : fr.2 p = [] := fire_push0 hf (P.houts l r e1 hr)
        refine ⟨_, 1, Run.cons l hs2 (Run.refl _), Lt, hLt, applyF_agree hA fr, ?_, ?_, ?_⟩
        · rw [applyF_app hf (nin_of hrd (by simp)), hpp, hpv, List.append_nil]
        · rw [applyF_app hf' (nin_of hrd (by simp)), hpp, hp', List.append_nil]
        · intro j hj
          have hc : (a0 :: ar)[j] ∈ a0 :: ar := List.getElem_mem hj
          rw [applyF_app hf (nin_of hrd (List.mem_cons_of_mem _ hc)),
            applyF_app hf' (nin_of hrd (List.mem_cons_of_mem _ hc)), has j hj, List.append_assoc]

theorem ab_bwd_term (P : PatAB rs rs' lp lq p q a0 ar bs f g) :
    ∀ σ' σ, RelAB p (a0 :: ar) f σ σ' → Terminal (step (graph rs')) σ' →
      ∃ u n, Run (step (graph rs)) σ n u ∧ Terminal (step (graph rs)) u ∧ Agree (p :: a0 :: ar) σ' u := by
  intro σ' σ ⟨Lt, hLt, hA, hpv, hp', has⟩ hT
  have hq := hT lq
  rw [step_graph P.hq'] at hq
  have hdis : ∃ c ∈ bs ++ a0 :: ar, σ' c = [] := by
    by_cases hall : ∀ c ∈ bs ++ a0 :: ar, σ' c ≠ []
    · rw [fire_comp hall] at hq; cases hq
    · exact exists_empty hall
  have outs : ∀ τ : Store Nat Nat, Agree (p :: a0 :: ar) σ τ → ∀ l, l ≠ lp → l ≠ lq →
      step (graph rs) τ l = none := by
    intro τ hτ l e1 e2
    cases hr : rs[l]? with
    | none => exact none_none hr τ
    | some r =>
      obtain ⟨hr', hrd⟩ := P.out e1 e2 hr
      have hA2 : Agree (p :: a0 :: ar) σ' τ := fun c hc => by rw [hτ c hc, hA c hc]
      exact outside_none hr' hr hrd hA2 (hT l)
  obtain ⟨c, hc, he⟩ := hdis
  rcases List.mem_append.mp hc with hb | ha
  · -- some b is empty: the reader stays disabled; drain f
    have hnd : c ∉ p :: a0 :: ar := fun h => by
      rcases List.mem_cons.mp h with h | h
      · exact P.p_nin_bs (h ▸ hb)
      · exact P.bs_as hb h
    obtain ⟨τ, n, hrun, ⟨d, hd, hτd⟩, hAτ⟩ := drain_comp P.hp P.p_nin_as _ σ rfl
    refine ⟨τ, n, hrun, ?_, ?_⟩
    · intro l
      by_cases e1 : l = lp
      · rw [e1, step_graph P.hp, fire_comp_none hd hτd]; rfl
      · by_cases e2 : l = lq
        · rw [e2, step_graph P.hq, fire_comp_none (List.mem_append_left _ hb) (by
            rw [hAτ c hnd, ← hA c hnd]; exact he)]; rfl
        · exact outs τ hAτ l e1 e2
    · intro d hd; rw [hAτ d hd, hA d hd]
  · -- an ai is empty in rs': nothing is pending, p is empty, f is disabled
    obtain ⟨j, hj, rfl⟩ := mem_pos ha
    rw [has j hj] at he
    have hL : Lt = [] := by
      cases Lt with
      | nil => rfl
      | cons _ _ => simp at he
    subst hL
    have hσc : σ (a0 :: ar)[j] = [] := by simpa using he
    refine ⟨σ, 0, Run.refl _, ?_, hA.symm⟩
    intro l
    by_cases e1 : l = lp
    · rw [e1, step_graph P.hp, fire_comp_none ha hσc]; rfl
    · by_cases e2 : l = lq
      · rw [e2, step_graph P.hq, fire_comp_none (List.mem_append_right bs (List.mem_singleton_self p))
          (by rw [hpv]; rfl)]; rfl
      · exact outs σ (fun _ _ => rfl) l e1 e2

theorem relAB_init {σ0 : Store Nat Nat} (h0 : σ0 p = []) : RelAB p (a0 :: ar) f σ0 σ0 :=
  ⟨[], by simp, fun _ _ => rfl, by rw [h0]; rfl, h0, fun _ _ => rfl⟩

theorem ab_forward (P : PatAB rs rs' lp lq p q a0 ar bs f g) {σ0 t : Store Nat Nat} {n : Nat}
    (h0 : σ0 p = []) (hr : Run (step (graph rs)) σ0 n t) (ht : Terminal (step (graph rs)) t) :
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧ Agree (p :: a0 :: ar) t t' :=
  sim_complete (RelAB p (a0 :: ar) f) (Agree (p :: a0 :: ar)) (ab_fwd_step P) (ab_fwd_term P) hr ht σ0
    (relAB_init h0)

theorem ab_backward (P : PatAB rs rs' lp lq p q a0 ar bs f g) {σ0 t' : Store Nat Nat} {n : Nat}
    (h0 : σ0 p = []) (hr : Run (step (graph rs')) σ0 n t') (ht : Terminal (step (graph rs')) t') :
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧ Agree (p :: a0 :: ar) t' t :=
  sim_complete (fun σ' σ => RelAB p (a0 :: ar) f σ σ') (Agree (p :: a0 :: ar))
    (fun σ' σ l u' hR hs => ab_bwd_step P σ' σ l u' hR hs) (fun σ' σ hR hT => ab_bwd_term P σ' σ hR hT)
    hr ht σ0 (relAB_init h0)

end AB

end Formal.Rewrite.Steps
