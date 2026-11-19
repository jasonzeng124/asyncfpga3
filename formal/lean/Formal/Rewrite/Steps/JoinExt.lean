import Formal.Rewrite.Steps.Dedupe
import Formal.Rewrite.ChanInv

/-!
# Formal.Rewrite.Steps.JoinExt — pattern and invariant of the join extension (shard A, 2026-11-19)

The pattern `PatJE` and the counting invariant `InvJ` of the "join extension" step; the simulation theorems
(`je_forward`, `je_backward`) and the problem statement are in `Formal.Rewrite.Steps.JoinExtSim`.

`rs` holds `fork x xs` (`x1, x2 ∈ xs`), `fork n ns` (`n1 ∈ ns`), `comp [x1, n1] c G`, `fork c cs` (`cc ∈ cs`),
`branch cc u t f`, `comp [x2] u F`; `rs'` is equal except `fork n (n2 :: ns)` and `comp [x2, n2] u F'`.
`InvJ` (an invariant of every run of `rs'` from empty internal channels): `|x2| + |u| = |x1| + |c| + |cc|` and
`|n2| + |u| = |n1| + |c| + |cc|`.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

/-- Close `a ≠ b` from a hypothesis `a ≠ b` or `b ≠ a`. -/
macro "nd" : tactic => `(tactic| first | assumption | exact Ne.symm (by assumption))

/-! ## Inversions of single firings -/

theorem fork_inv {i : Nat} {os : List Nat} {σ : Store Nat Nat} {fr : Fire Nat Nat}
    (h : (Rule.fork i os).fire natVI σ = some fr) :
    ∃ v vs, σ i = v :: vs ∧ fr = (popOf [i], fun c => if c ∈ os then [v] else []) := by
  cases hi : σ i with
  | nil => rw [fire_fork_none hi] at h; cases h
  | cons v vs => rw [fire_fork hi] at h; exact ⟨v, vs, rfl, (Option.some.inj h).symm⟩

theorem fork_none_inv {i : Nat} {os : List Nat} {σ : Store Nat Nat}
    (h : (Rule.fork i os).fire natVI σ = none) : σ i = [] := by
  cases hi : σ i with
  | nil => rfl
  | cons v vs => rw [fire_fork hi] at h; cases h

theorem comp_inv {ins : List Nat} {o : Nat} {F : E} {σ : Store Nat Nat} {fr : Fire Nat Nat}
    (h : (Rule.comp ins o F).fire natVI σ = some fr) :
    (∀ c ∈ ins, σ c ≠ []) ∧ fr = (popOf ins, fun c => if c = o then [F.eval (ins.map (hd σ))] else []) := by
  by_cases hall : ∀ c ∈ ins, σ c ≠ []
  · rw [fire_comp hall] at h; exact ⟨hall, (Option.some.inj h).symm⟩
  · obtain ⟨c, hc, he⟩ := exists_empty hall; rw [fire_comp_none hc he] at h; cases h

/-- What a branch pushes, given its condition `b` and data `y`. -/
def brOut (t f b y : Nat) : Nat → List Nat :=
  fun ch => (if ch = t ∧ b % 2 = 1 then [y] else []) ++ (if ch = f ∧ ¬ b % 2 = 1 then [y] else [])

theorem branch_inv {c d t f : Nat} {σ : Store Nat Nat} {fr : Fire Nat Nat}
    (h : (Rule.branch c d t f).fire natVI σ = some fr) :
    ∃ b bs y ys, σ c = b :: bs ∧ σ d = y :: ys ∧ fr = (popOf [c, d], brOut t f b y) :=
  Formal.Rewrite.ChanInv.fire_branch h

theorem branch_some {c d t f : Nat} {σ : Store Nat Nat} {b y : Nat} {bs ys : List Nat}
    (hc : σ c = b :: bs) (hd : σ d = y :: ys) :
    (Rule.branch c d t f).fire natVI σ = some (popOf [c, d], brOut t f b y) := by
  have hs : ∃ fr, (Rule.branch c d t f).fire natVI σ = some fr := by
    simp [Rule.fire, strictF, Rule.insL, heads, hc, hd, Rule.out, natVI]
  obtain ⟨fr, hfr⟩ := hs
  obtain ⟨b', bs', y', ys', hb, hy, rfl⟩ := branch_inv hfr
  rw [hc] at hb; rw [hd] at hy
  injection hb with e1 _; injection hy with e2 _
  subst e1; subst e2; exact hfr

theorem branch_none {c d t f : Nat} {σ : Store Nat Nat} (h : σ c = [] ∨ σ d = []) :
    (Rule.branch c d t f).fire natVI σ = none := by
  cases hfr : (Rule.branch c d t f).fire natVI σ with
  | none => rfl
  | some fr =>
    obtain ⟨b, bs, y, ys, hb, hy, -⟩ := branch_inv hfr
    rcases h with h | h
    · rw [hb] at h; cases h
    · rw [hy] at h; cases h

theorem branch_none_inv {c d t f : Nat} {σ : Store Nat Nat} (h : (Rule.branch c d t f).fire natVI σ = none) :
    σ c = [] ∨ σ d = [] := by
  cases hc : σ c with
  | nil => exact Or.inl rfl
  | cons b bs =>
    cases hd : σ d with
    | nil => exact Or.inr rfl
    | cons y ys => rw [branch_some hc hd] at h; cases h

theorem branch_at {c d t f b y : Nat} {σ : Store Nat Nat} (_hcd : c ≠ d) (ch : Nat) :
    applyF σ (popOf [c, d], brOut t f b y) ch =
      (if ch = c ∨ ch = d then (σ ch).tail else σ ch) ++ brOut t f b y ch := by
  simp only [applyF_at, popOf, List.mem_cons, List.not_mem_nil, or_false]
  by_cases h : ch = c ∨ ch = d
  · simp [h, List.drop_one]
  · simp [h]

theorem brOut_nil {t f b y ch : Nat} (ht : ch ≠ t) (hf : ch ≠ f) : brOut t f b y ch = [] := by
  simp [brOut, ht, hf]

theorem step_some_inv {rs : List Rule} {l : Nat} {r : Rule} (hr : rs[l]? = some r) {σ σ1 : Store Nat Nat}
    (h : step (graph rs) σ l = some σ1) : ∃ fr, r.fire natVI σ = some fr ∧ σ1 = applyF σ fr := by
  rw [step_graph hr] at h
  cases hf : r.fire natVI σ with
  | none => rw [hf] at h; cases h
  | some fr => rw [hf] at h; exact ⟨fr, rfl, (Option.some.inj h).symm⟩

theorem step_none_inv {rs : List Rule} {l : Nat} {r : Rule} (hr : rs[l]? = some r) {σ : Store Nat Nat}
    (h : step (graph rs) σ l = none) : r.fire natVI σ = none := by
  rw [step_graph hr] at h
  cases hf : r.fire natVI σ with
  | none => rfl
  | some fr => rw [hf] at h; cases h

theorem step_of_fire {rs : List Rule} {l : Nat} {r : Rule} (hr : rs[l]? = some r) {σ : Store Nat Nat}
    {fr : Fire Nat Nat} (h : r.fire natVI σ = some fr) : step (graph rs) σ l = some (applyF σ fr) := by
  rw [step_graph hr, h]; rfl

theorem step_none_of {rs : List Rule} {l : Nat} {r : Rule} (hr : rs[l]? = some r) {σ : Store Nat Nat}
    (h : r.fire natVI σ = none) : step (graph rs) σ l = none := by
  rw [step_graph hr, h]; rfl

theorem cons_of_ne {σ : Store Nat Nat} {ch : Nat} (h : σ ch ≠ []) : ∃ v vs, σ ch = v :: vs := by
  cases e : σ ch with
  | nil => exact absurd e h
  | cons v vs => exact ⟨v, vs, rfl⟩

theorem ne_of_len {l : List Nat} (h : l.length ≠ 0) : l ≠ [] := fun e => h (by rw [e]; rfl)

/-! ## The pattern -/

structure PatJE (rs rs' : List Rule) (lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f : Nat)
    (xs ns cs : List Nat) (G F F' : E) : Prop where
  hx : rs[lx]? = some (.fork x xs)
  hn : rs[ln]? = some (.fork n ns)
  hn' : rs'[ln]? = some (.fork n (n2 :: ns))
  hc : rs[lc]? = some (.comp [x1, n1] c G)
  hk : rs[lk]? = some (.fork c cs)
  hb : rs[lb]? = some (.branch cc u t f)
  hu : rs[lu]? = some (.comp [x2] u F)
  hu' : rs'[lu]? = some (.comp [x2, n2] u F')
  hsame : ∀ l, l ≠ ln → l ≠ lu → rs'[l]? = rs[l]?
  hlab : [lx, ln, lc, lk, lb, lu].Nodup
  /-- No other rule touches the seven internal channels. -/
  hout : ∀ l r, l ≠ lx → l ≠ ln → l ≠ lc → l ≠ lk → l ≠ lb → l ≠ lu → rs[l]? = some r →
    ∀ ch ∈ [x1, x2, n1, n2, c, cc, u], ch ∉ r.insL ∧ ch ∉ r.outsL
  hnd : [x, n, x1, x2, n1, n2, c, cc, u].Nodup
  hxs : x1 ∈ xs ∧ x2 ∈ xs ∧ x ∉ xs ∧ n1 ∉ xs ∧ n2 ∉ xs ∧ c ∉ xs ∧ cc ∉ xs ∧ u ∉ xs
  hns : n1 ∈ ns ∧ n ∉ ns ∧ x1 ∉ ns ∧ x2 ∉ ns ∧ n2 ∉ ns ∧ c ∉ ns ∧ cc ∉ ns ∧ u ∉ ns
  hcs : cc ∈ cs ∧ c ∉ cs ∧ x1 ∉ cs ∧ x2 ∉ cs ∧ n1 ∉ cs ∧ n2 ∉ cs ∧ u ∉ cs
  ht : t ∉ [x1, x2, n1, n2, c, cc, u]
  hf : f ∉ [x1, x2, n1, n2, c, cc, u]
  hF : ∀ v w, F'.eval [v, w] = F.eval [v]

/-- The counting invariant of `rs'`. -/
def InvJ (x1 x2 n1 n2 c cc u : Nat) (σ : Store Nat Nat) : Prop :=
  (σ x2).length + (σ u).length = (σ x1).length + (σ c).length + (σ cc).length ∧
  (σ n2).length + (σ u).length = (σ n1).length + (σ c).length + (σ cc).length

section JE

macro "jdist " P:term : tactic => `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
  _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := ($P).dist)
macro "jldist " P:term : tactic => `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := ($P).ldist)

variable {rs rs' : List Rule} {lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f : Nat} {xs ns cs : List Nat}
  {G F F' : E}

/-- All pairwise distinctness facts of the nine channels. -/
theorem PatJE.dist (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F') :
    x ≠ n ∧ x ≠ x1 ∧ x ≠ x2 ∧ x ≠ n1 ∧ x ≠ n2 ∧ x ≠ c ∧ x ≠ cc ∧ x ≠ u ∧
    n ≠ x1 ∧ n ≠ x2 ∧ n ≠ n1 ∧ n ≠ n2 ∧ n ≠ c ∧ n ≠ cc ∧ n ≠ u ∧
    x1 ≠ x2 ∧ x1 ≠ n1 ∧ x1 ≠ n2 ∧ x1 ≠ c ∧ x1 ≠ cc ∧ x1 ≠ u ∧
    x2 ≠ n1 ∧ x2 ≠ n2 ∧ x2 ≠ c ∧ x2 ≠ cc ∧ x2 ≠ u ∧
    n1 ≠ n2 ∧ n1 ≠ c ∧ n1 ≠ cc ∧ n1 ≠ u ∧
    n2 ≠ c ∧ n2 ≠ cc ∧ n2 ≠ u ∧ c ≠ cc ∧ c ≠ u ∧ cc ≠ u := by
  have h := P.hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3, b4, b5, b6, b7⟩, ⟨c1, c2, c3, c4, c5, c6⟩,
    ⟨d1, d2, d3, d4, d5⟩, ⟨e1, e2, e3, e4⟩, ⟨f1, f2, f3⟩, ⟨g1, g2⟩, h1, -⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, c1, c2, c3, c4, c5, c6, d1, d2, d3, d4, d5,
    e1, e2, e3, e4, f1, f2, f3, g1, g2, h1⟩

theorem PatJE.ldist (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F') :
    lx ≠ ln ∧ lx ≠ lc ∧ lx ≠ lk ∧ lx ≠ lb ∧ lx ≠ lu ∧ ln ≠ lc ∧ ln ≠ lk ∧ ln ≠ lb ∧ ln ≠ lu ∧
    lc ≠ lk ∧ lc ≠ lb ∧ lc ≠ lu ∧ lk ≠ lb ∧ lk ≠ lu ∧ lb ≠ lu := by
  have h := P.hlab
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3⟩, ⟨d1, d2⟩, e1, -⟩ := h
  exact ⟨a1, a2, a3, a4, a5, b1, b2, b3, b4, c1, c2, c3, d1, d2, e1⟩

theorem PatJE.tf (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F') :
    x1 ≠ t ∧ x2 ≠ t ∧ n1 ≠ t ∧ n2 ≠ t ∧ c ≠ t ∧ cc ≠ t ∧ u ≠ t ∧
    x1 ≠ f ∧ x2 ≠ f ∧ n1 ≠ f ∧ n2 ≠ f ∧ c ≠ f ∧ cc ≠ f ∧ u ≠ f := by
  have h1 := P.ht; have h2 := P.hf
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 h2
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h1; obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h2
  exact ⟨Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4, Ne.symm a5, Ne.symm a6, Ne.symm a7,
    Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm b6, Ne.symm b7⟩

/-- The rules of `rs'`, by label. -/
theorem PatJE.rx' (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F') :
    rs'[lx]? = some (.fork x xs) := by
  rw [P.hsame lx P.ldist.1 P.ldist.2.2.2.2.1]; exact P.hx
theorem PatJE.rc' (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F') :
    rs'[lc]? = some (.comp [x1, n1] c G) := by
  jldist P; rw [P.hsame lc (by nd) (by nd)]; exact P.hc
theorem PatJE.rk' (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F') :
    rs'[lk]? = some (.fork c cs) := by
  jldist P; rw [P.hsame lk (by nd) (by nd)]; exact P.hk
theorem PatJE.rb' (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F') :
    rs'[lb]? = some (.branch cc u t f) := by
  jldist P; rw [P.hsame lb (by nd) (by nd)]; exact P.hb

/-- Every rule other than the `n` fork, the update and the branch reads none of `x2 n2 u` and writes no `u`. -/
theorem PatJE.other (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F')
    {l : Nat} {r : Rule} (hln : l ≠ ln) (hlb : l ≠ lb) (hlu : l ≠ lu) (hr : rs[l]? = some r) :
    (∀ ch ∈ r.insL, ch ∉ [x2, n2, u]) ∧ u ∉ r.outsL := by
  jdist P
  by_cases e1 : l = lx
  · subst e1; rw [P.hx] at hr; obtain rfl := Option.some.inj hr
    refine ⟨fun ch hc => ?_, P.hxs.2.2.2.2.2.2.2⟩
    simp only [Rule.insL, List.mem_singleton] at hc; subst hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; refine ⟨?_, ?_, ?_⟩ <;> nd
  by_cases e2 : l = lc
  · subst e2; rw [P.hc] at hr; obtain rfl := Option.some.inj hr
    refine ⟨fun ch hc => ?_, ?_⟩
    · simp only [Rule.insL, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; refine ⟨?_, ?_, ?_⟩ <;> nd)
    · simp only [Rule.outsL, List.mem_singleton]; nd
  by_cases e3 : l = lk
  · subst e3; rw [P.hk] at hr; obtain rfl := Option.some.inj hr
    refine ⟨fun ch hc => ?_, P.hcs.2.2.2.2.2.2⟩
    simp only [Rule.insL, List.mem_singleton] at hc; subst hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; refine ⟨?_, ?_, ?_⟩ <;> nd
  have ho := P.hout l r e1 hln e2 e3 hlb hlu hr
  refine ⟨fun ch hc hm => ?_, (ho u (by simp)).2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact (ho ch (by simp)).1 hc
  · exact (ho ch (by simp)).1 hc
  · exact (ho ch (by simp)).1 hc

theorem PatJE.reads_n2 (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F')
    {l : Nat} {r : Rule} (hln : l ≠ ln) (hlu : l ≠ lu) (hr : rs[l]? = some r) : ∀ ch ∈ r.insL, ch ∉ [n2] := by
  jdist P
  by_cases e : l = lb
  · subst e; rw [P.hb] at hr; obtain rfl := Option.some.inj hr
    intro ch hc
    simp only [Rule.insL, List.mem_cons, List.not_mem_nil, or_false] at hc
    simp only [List.mem_singleton]
    rcases hc with rfl | rfl <;> nd
  · intro ch hc hm
    simp only [List.mem_singleton] at hm; subst hm
    exact (P.other hln e hlu hr).1 _ hc (by simp)

/-! ## The invariant is preserved by every step of `rs'` -/

theorem invJ_step (P : PatJE rs rs' lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u t f xs ns cs G F F')
    {σ σ1 : Store Nat Nat} {l : Nat} (hI : InvJ x1 x2 n1 n2 c cc u σ) (hs : step (graph rs') σ l = some σ1) :
    InvJ x1 x2 n1 n2 c cc u σ1 := by
  jdist P; have T := P.tf
  obtain ⟨h1, h2⟩ := hI
  unfold InvJ
  by_cases e1 : l = ln
  · subst e1
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.hn' hs
    obtain ⟨v, vs, hv, rfl⟩ := fork_inv hf
    have hi : n ∉ n2 :: ns := by
      simp only [List.mem_cons, not_or]; exact ⟨by nd, P.hns.2.1⟩
    have hns := P.hns
    simp only [fork_at hi]
    simp only [List.mem_cons]
    simp [show x1 ≠ n by nd, show x2 ≠ n by nd, show n1 ≠ n by nd, show n2 ≠ n by nd,
      show c ≠ n by nd, show cc ≠ n by nd, show u ≠ n by nd, show x1 ≠ n2 by nd,
      show x2 ≠ n2 by nd, show c ≠ n2 by nd, show cc ≠ n2 by nd, show u ≠ n2 by nd,
      show n1 ≠ n2 by nd, hns.1, hns.2.2.1, hns.2.2.2.1, hns.2.2.2.2.2.1, hns.2.2.2.2.2.2.1,
      hns.2.2.2.2.2.2.2]
    omega
  by_cases e2 : l = lu
  · subst e2
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.hu' hs
    obtain ⟨hall, rfl⟩ := comp_inv hf
    have hx2 := hall x2 (by simp); have hn2 := hall n2 (by simp)
    have ho : u ∉ [x2, n2] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; refine ⟨?_, ?_⟩ <;> nd
    simp only [comp_atv ho]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    simp [show x1 ≠ x2 by nd, show x1 ≠ n2 by nd, show x1 ≠ u by nd, show n1 ≠ x2 by nd,
      show n1 ≠ n2 by nd, show n1 ≠ u by nd, show c ≠ x2 by nd, show c ≠ n2 by nd,
      show c ≠ u by nd, show cc ≠ x2 by nd, show cc ≠ n2 by nd, show cc ≠ u by nd,
      show x2 ≠ n2 by nd, show n2 ≠ x2 by nd, show u ≠ x2 by nd, show u ≠ n2 by nd]
    have l1 : (σ x2).length ≠ 0 := fun h => hx2 (List.eq_nil_of_length_eq_zero h)
    have l2 : (σ n2).length ≠ 0 := fun h => hn2 (List.eq_nil_of_length_eq_zero h)
    omega
  by_cases e3 : l = lb
  · subst e3
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.rb' hs
    obtain ⟨b, bs, y, ys, hb, hy, rfl⟩ := branch_inv hf
    simp only [branch_at (show cc ≠ u by nd)]
    rw [brOut_nil T.1 T.2.2.2.2.2.2.2.1, brOut_nil T.2.1 T.2.2.2.2.2.2.2.2.1,
      brOut_nil T.2.2.1 T.2.2.2.2.2.2.2.2.2.1, brOut_nil T.2.2.2.1 T.2.2.2.2.2.2.2.2.2.2.1,
      brOut_nil T.2.2.2.2.1 T.2.2.2.2.2.2.2.2.2.2.2.1, brOut_nil T.2.2.2.2.2.1 T.2.2.2.2.2.2.2.2.2.2.2.2.1,
      brOut_nil T.2.2.2.2.2.2.1 T.2.2.2.2.2.2.2.2.2.2.2.2.2]
    simp [show x1 ≠ cc by nd, show x1 ≠ u by nd, show x2 ≠ cc by nd, show x2 ≠ u by nd,
      show n1 ≠ cc by nd, show n1 ≠ u by nd, show n2 ≠ cc by nd, show n2 ≠ u by nd,
      show c ≠ cc by nd, show c ≠ u by nd, hb, hy]
    rw [hb, hy] at h1 h2; simp only [List.length_cons] at h1 h2
    omega
  by_cases e4 : l = lx
  · subst e4
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.rx' hs
    obtain ⟨v, vs, hv, rfl⟩ := fork_inv hf
    have hxs := P.hxs
    simp only [fork_at hxs.2.2.1]
    simp [show x1 ≠ x by nd, show x2 ≠ x by nd, show n1 ≠ x by nd, show n2 ≠ x by nd,
      show c ≠ x by nd, show cc ≠ x by nd, show u ≠ x by nd, hxs.1, hxs.2.1, hxs.2.2.2.1,
      hxs.2.2.2.2.1, hxs.2.2.2.2.2.1, hxs.2.2.2.2.2.2.1, hxs.2.2.2.2.2.2.2]
    omega
  by_cases e5 : l = lc
  · subst e5
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.rc' hs
    obtain ⟨hall, rfl⟩ := comp_inv hf
    have hx1 := hall x1 (by simp); have hn1 := hall n1 (by simp)
    have ho : c ∉ [x1, n1] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; refine ⟨?_, ?_⟩ <;> nd
    simp only [comp_atv ho]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    simp [show x2 ≠ x1 by nd, show x2 ≠ n1 by nd, show x2 ≠ c by nd, show n2 ≠ x1 by nd,
      show n2 ≠ n1 by nd, show n2 ≠ c by nd, show u ≠ x1 by nd, show u ≠ n1 by nd,
      show u ≠ c by nd, show cc ≠ x1 by nd, show cc ≠ n1 by nd, show cc ≠ c by nd,
      show x1 ≠ n1 by nd, show n1 ≠ x1 by nd, show c ≠ x1 by nd, show c ≠ n1 by nd]
    have l1 : (σ x1).length ≠ 0 := fun h => hx1 (List.eq_nil_of_length_eq_zero h)
    have l2 : (σ n1).length ≠ 0 := fun h => hn1 (List.eq_nil_of_length_eq_zero h)
    omega
  by_cases e6 : l = lk
  · subst e6
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.rk' hs
    obtain ⟨v, vs, hv, rfl⟩ := fork_inv hf
    have hcs := P.hcs
    simp only [fork_at hcs.2.1]
    simp [show x1 ≠ c by nd, show x2 ≠ c by nd, show n1 ≠ c by nd, show n2 ≠ c by nd,
      show cc ≠ c by nd, show u ≠ c by nd, hcs.1, hcs.2.2.1, hcs.2.2.2.1, hcs.2.2.2.2.1,
      hcs.2.2.2.2.2.1, hcs.2.2.2.2.2.2, hv]
    rw [hv] at h1 h2; simp only [List.length_cons] at h1 h2
    omega
  -- any other rule leaves the seven channels alone
  cases hr : rs[l]? with
  | none => rw [step_graph_none (by rw [P.hsame l e1 e2]; exact hr)] at hs; cases hs
  | some r =>
    have hr' : rs'[l]? = some r := by rw [P.hsame l e1 e2]; exact hr
    obtain ⟨fr, hf, rfl⟩ := step_some_inv hr' hs
    have ho := P.hout l r e4 e1 e5 e6 e3 e2 hr
    have keep : ∀ ch ∈ [x1, x2, n1, n2, c, cc, u], applyF σ fr ch = σ ch := by
      intro ch hch
      rw [applyF_app hf (ho ch hch).1, fire_push0 hf (ho ch hch).2, List.append_nil]
    rw [keep x1 (by simp), keep x2 (by simp), keep n1 (by simp), keep n2 (by simp), keep c (by simp),
      keep cc (by simp), keep u (by simp)]
    exact ⟨h1, h2⟩

end JE

end Formal.Rewrite.Steps
