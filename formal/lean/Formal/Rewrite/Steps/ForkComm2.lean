import Formal.Rewrite.Steps.JoinExt

/-!
# Formal.Rewrite.Steps.ForkComm2 — a fork after a two-input comp is two forks before two copies of it (shard A, 2026-11-19)

**Problem, plainly.** A comp computes `y = G(x, n)` and a fork copies `y` onto `y0` and `y1`. Is that the same, whatever
surrounds it, as forking `x` onto `x0, x1` and `n` onto `n0, n1`, then `y0 = G(x0, n0)` and `y1 = G(x1, n1)`? This is
the step that unpacks research's `BDC_RING_FUSE` cell (one comp waiting for `x` and `n`, whose packed result is
forked to the update's and the test's slices) into two comps that the join-extension step (`JoinExtSim`) then relates
to the unfused graph. It is `ForkComm` with two inputs; the copies may now drift apart (one copy can run ahead of the
other, and the `x` fork ahead of the `n` fork).

**Proved** (`fc2_forward`, `fc2_backward`): for ANY imported graph `rs` holding `comp [x, n] y G` at `lc` and
`fork y [y0, y1]` at `lf`, and `rs'` equal except `fork x [x0, x1]` at `lc`, `fork n [n0, n1]` at `lf`,
`comp [x0, n0] y0 G` at `la` and `comp [x1, n1] y1 G` at `lb` (labels unused in `rs`), with the nine channels distinct,
no other rule reading `x n y x0 x1 n0 n1` and no other rule writing `y x0 x1 n0 n1 y0 y1`: from any store with
`y x0 x1 n0 n1` empty, every complete run of either graph is matched by a complete run of the other ending in the
same store outside `x n y x0 x1 n0 n1`.

**How.** Forward, `rs'` fires both forks when `rs` fires the comp and both comps when `rs` fires the fork. Backward,
`rs` fires its comp and fork only when the first of the two `rs'` comps fires on a pair; `A`/`B` are the `x`/`n`
values `rs'` has forked and `rs` not yet consumed, `Q0`/`Q1` the pairs `rs` has computed and one `rs'` comp has not.

**Not covered:** token level only; more than two inputs.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

structure PatFC2 (rs rs' : List Rule) (lc lf la lb x n y x0 x1 n0 n1 y0 y1 : Nat) (G : E) : Prop where
  hc : rs[lc]? = some (.comp [x, n] y G)
  hf : rs[lf]? = some (.fork y [y0, y1])
  ha : rs[la]? = none
  hb : rs[lb]? = none
  hc' : rs'[lc]? = some (.fork x [x0, x1])
  hf' : rs'[lf]? = some (.fork n [n0, n1])
  ha' : rs'[la]? = some (.comp [x0, n0] y0 G)
  hb' : rs'[lb]? = some (.comp [x1, n1] y1 G)
  hab : la ≠ lb
  hsame : ∀ l, l ≠ lc → l ≠ lf → l ≠ la → l ≠ lb → rs'[l]? = rs[l]?
  hins : ∀ l r, l ≠ lc → l ≠ lf → rs[l]? = some r → ∀ ch ∈ r.insL, ch ∉ [x, n, y, x0, x1, n0, n1]
  houts : ∀ l r, l ≠ lc → l ≠ lf → rs[l]? = some r → ∀ ch ∈ r.outsL, ch ∉ [y, x0, x1, n0, n1, y0, y1]
  hnd : [x, n, y, x0, x1, n0, n1, y0, y1].Nodup

/-- The pairwise function. -/
def g2 (G : E) (a b : Nat) : Nat := G.eval [a, b]

section FC2

macro "fdist " P:term : tactic => `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
  _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := ($P).dist)

variable {rs rs' : List Rule} {lc lf la lb x n y x0 x1 n0 n1 y0 y1 : Nat} {G : E}

theorem PatFC2.dist (P : PatFC2 rs rs' lc lf la lb x n y x0 x1 n0 n1 y0 y1 G) :
    x ≠ n ∧ x ≠ y ∧ x ≠ x0 ∧ x ≠ x1 ∧ x ≠ n0 ∧ x ≠ n1 ∧ x ≠ y0 ∧ x ≠ y1 ∧
    n ≠ y ∧ n ≠ x0 ∧ n ≠ x1 ∧ n ≠ n0 ∧ n ≠ n1 ∧ n ≠ y0 ∧ n ≠ y1 ∧
    y ≠ x0 ∧ y ≠ x1 ∧ y ≠ n0 ∧ y ≠ n1 ∧ y ≠ y0 ∧ y ≠ y1 ∧
    x0 ≠ x1 ∧ x0 ≠ n0 ∧ x0 ≠ n1 ∧ x0 ≠ y0 ∧ x0 ≠ y1 ∧
    x1 ≠ n0 ∧ x1 ≠ n1 ∧ x1 ≠ y0 ∧ x1 ≠ y1 ∧
    n0 ≠ n1 ∧ n0 ≠ y0 ∧ n0 ≠ y1 ∧ n1 ≠ y0 ∧ n1 ≠ y1 ∧ y0 ≠ y1 := by
  have h := P.hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3, b4, b5, b6, b7⟩, ⟨c1, c2, c3, c4, c5, c6⟩,
    ⟨d1, d2, d3, d4, d5⟩, ⟨e1, e2, e3, e4⟩, ⟨f1, f2, f3⟩, ⟨g1, g2⟩, h1, -⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, c1, c2, c3, c4, c5, c6, d1, d2, d3, d4, d5,
    e1, e2, e3, e4, f1, f2, f3, g1, g2, h1⟩

theorem PatFC2.labs (P : PatFC2 rs rs' lc lf la lb x n y x0 x1 n0 n1 y0 y1 G) :
    lc ≠ lf ∧ la ≠ lc ∧ la ≠ lf ∧ lb ≠ lc ∧ lb ≠ lf := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · have h1 := P.hc; rw [e, P.hf] at h1; cases h1
  · have h1 := P.ha; rw [e, P.hc] at h1; cases h1
  · have h1 := P.ha; rw [e, P.hf] at h1; cases h1
  · have h1 := P.hb; rw [e, P.hc] at h1; cases h1
  · have h1 := P.hb; rw [e, P.hf] at h1; cases h1

/-- A label holding a rule in `rs` other than the comp and the fork holds the same rule in `rs'`. -/
theorem PatFC2.oth (P : PatFC2 rs rs' lc lf la lb x n y x0 x1 n0 n1 y0 y1 G) {l : Nat} {r : Rule}
    (e1 : l ≠ lc) (e2 : l ≠ lf) (hr : rs[l]? = some r) : rs'[l]? = some r := by
  have ea : l ≠ la := fun e => by rw [e, P.ha] at hr; cases hr
  have eb : l ≠ lb := fun e => by rw [e, P.hb] at hr; cases hr
  rw [P.hsame l e1 e2 ea eb]; exact hr

theorem zw_snoc {A B : List Nat} (h : A.length = B.length) (f : Nat → Nat → Nat) (a b : Nat) :
    List.zipWith f (A ++ [a]) (B ++ [b]) = List.zipWith f A B ++ [f a b] := by
  rw [List.zipWith_append h]; rfl

/-! ## Forward: `rs'` fires both forks with the comp, both comps with the fork -/

def RelF2 (y x0 x1 n0 n1 : Nat) (G : E) (σ σ' : Store Nat Nat) : Prop :=
  Agree [y, x0, x1, n0, n1] σ σ' ∧ σ' y = [] ∧ σ' x1 = σ' x0 ∧ σ' n1 = σ' n0 ∧
  (σ' x0).length = (σ' n0).length ∧ σ y = List.zipWith (g2 G) (σ' x0) (σ' n0)

theorem fc2_fwd_step (P : PatFC2 rs rs' lc lf la lb x n y x0 x1 n0 n1 y0 y1 G) :
    ∀ σ σ' l σ1, RelF2 y x0 x1 n0 n1 G σ σ' → step (graph rs) σ l = some σ1 →
      ∃ σ1' k, Run (step (graph rs')) σ' k σ1' ∧ RelF2 y x0 x1 n0 n1 G σ1 σ1' := by
  intro σ σ' l σ1 ⟨hA, hy', h01, hn01, hlen, hy⟩ hs
  fdist P
  have nD : ∀ ch, ch ≠ y → ch ≠ x0 → ch ≠ x1 → ch ≠ n0 → ch ≠ n1 → σ' ch = σ ch := fun ch a1 a2 a3 a4 a5 =>
    hA ch (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨a1, a2, a3, a4, a5⟩)
  by_cases e1 : l = lc
  · subst e1
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.hc hs
    obtain ⟨hall, rfl⟩ := comp_inv hf
    obtain ⟨a, as, ha⟩ := cons_of_ne (hall x (by simp))
    obtain ⟨b, bs, hb⟩ := cons_of_ne (hall n (by simp))
    have ha' : σ' x = a :: as := by rw [nD x (by nd) (by nd) (by nd) (by nd) (by nd)]; exact ha
    have hb' : σ' n = b :: bs := by rw [nD n (by nd) (by nd) (by nd) (by nd) (by nd)]; exact hb
    have hix : x ∉ [x0, x1] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
    have hin : n ∉ [n0, n1] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
    have hs1 := step_of_fire P.hc' (fire_fork (os := [x0, x1]) ha')
    have k2 : ∀ ch, applyF σ' (popOf [x], fun ch => if ch ∈ [x0, x1] then [a] else []) ch =
        if ch = x then as else if ch = x0 ∨ ch = x1 then σ' ch ++ [a] else σ' ch := by
      intro ch; rw [fork_at hix]
      by_cases e : ch = x
      · subst e; simp [ha']
      · simp [e]
    generalize applyF σ' (popOf [x], fun ch => if ch ∈ [x0, x1] then [a] else []) = S2 at hs1 k2
    have hS2n : S2 n = b :: bs := by rw [k2]; simp [show n ≠ x by nd, show n ≠ x0 by nd, show n ≠ x1 by nd, hb']
    have hs2 := step_of_fire P.hf' (fire_fork (os := [n0, n1]) hS2n)
    have k3 : ∀ ch, applyF S2 (popOf [n], fun ch => if ch ∈ [n0, n1] then [b] else []) ch =
        if ch = n then bs else if ch = n0 ∨ ch = n1 then S2 ch ++ [b] else S2 ch := by
      intro ch; rw [fork_at hin]
      by_cases e : ch = n
      · subst e; simp [hS2n]
      · simp [e]
    generalize applyF S2 (popOf [n], fun ch => if ch ∈ [n0, n1] then [b] else []) = S3 at hs2 k3
    have hiy : y ∉ [x, n] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
    have hv : G.eval ([x, n].map (hd σ)) = g2 G a b := by simp [hd, ha, hb, g2]
    refine ⟨S3, 2, Run.cons _ hs1 (run_one hs2), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ch hch
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hch
      obtain ⟨c1, c2, c3, c4, c5⟩ := hch
      rw [k3, k2, comp_atv hiy]
      simp only [List.mem_cons, List.not_mem_nil, or_false, c1, c2, c3, c4, c5, false_or, or_false, ite_false]
      by_cases ex : ch = x
      · subst ex; simp [show ch ≠ n by nd, ha]
      · by_cases en : ch = n
        · subst en; simp [ex, hb]
        · simp [ex, en]; exact nD ch c1 c2 c3 c4 c5
    · rw [k3, k2]; simp [show y ≠ n by nd, show y ≠ n0 by nd, show y ≠ n1 by nd, show y ≠ x by nd,
        show y ≠ x0 by nd, show y ≠ x1 by nd, hy']
    · rw [k3, k3, k2, k2]
      simp [show x1 ≠ n by nd, show x1 ≠ n0 by nd, show x1 ≠ n1 by nd, show x1 ≠ x by nd,
        show x0 ≠ n by nd, show x0 ≠ n0 by nd, show x0 ≠ n1 by nd, show x0 ≠ x by nd, h01]
    · rw [k3, k3, k2, k2]
      simp [show n1 ≠ n by nd, show n0 ≠ n by nd, show n1 ≠ x by nd, show n1 ≠ x0 by nd, show n1 ≠ x1 by nd,
        show n0 ≠ x by nd, show n0 ≠ x0 by nd, show n0 ≠ x1 by nd, hn01]
    · rw [k3, k3, k2, k2]
      simp [show x0 ≠ n by nd, show x0 ≠ n0 by nd, show x0 ≠ n1 by nd, show x0 ≠ x by nd,
        show n0 ≠ n by nd, show n0 ≠ x by nd, show n0 ≠ x0 by nd, show n0 ≠ x1 by nd, hlen]
    · rw [comp_atv hiy, k3, k3, k2, k2]
      simp only [List.mem_cons, List.not_mem_nil, or_false, show y ≠ x by nd, show y ≠ n by nd, ite_true,
        ite_false, false_or]
      simp only [show x0 ≠ n by nd, show x0 ≠ n0 by nd, show x0 ≠ n1 by nd, show x0 ≠ x by nd,
        show n0 ≠ n by nd, show n0 ≠ x by nd, show n0 ≠ x0 by nd, show n0 ≠ x1 by nd, ite_true, ite_false,
        true_or, or_false, false_or]
      rw [hy, hv, zw_snoc hlen]
  by_cases e2 : l = lf
  · subst e2
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.hf hs
    obtain ⟨v, vs, hv, rfl⟩ := fork_inv hf
    rw [hv] at hy
    cases hx0 : σ' x0 with
    | nil => rw [hx0] at hy; cases hy
    | cons a X =>
    cases hn0 : σ' n0 with
    | nil => rw [hx0, hn0] at hy; cases hy
    | cons b N =>
    rw [hx0, hn0, List.zipWith_cons_cons] at hy
    injection hy with ev evs
    have hall0 : ∀ ch ∈ [x0, n0], σ' ch ≠ [] := by
      intro ch hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · rw [hx0]; exact List.cons_ne_nil _ _
      · rw [hn0]; exact List.cons_ne_nil _ _
    have hs1 := step_of_fire P.ha' (fire_comp hall0)
    have hg0 : G.eval ([x0, n0].map (hd σ')) = v := by simp [hd, hx0, hn0, ev, g2]
    rw [hg0] at hs1
    have hy0 : y0 ∉ [x0, n0] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
    have k2 := comp_atv (σ := σ') hy0 v
    generalize applyF σ' (popOf [x0, n0], fun ch => if ch = y0 then [v] else []) = S2 at hs1 k2
    have hall1 : ∀ ch ∈ [x1, n1], S2 ch ≠ [] := by
      intro ch hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · rw [k2]; simp [show ch ≠ x0 by nd, show ch ≠ n0 by nd, show ch ≠ y0 by nd, h01, hx0]
      · rw [k2]; simp [show ch ≠ x0 by nd, show ch ≠ n0 by nd, show ch ≠ y0 by nd, hn01, hn0]
    have hs2 := step_of_fire P.hb' (fire_comp hall1)
    have hg1 : G.eval ([x1, n1].map (hd S2)) = v := by
      rw [← hg0]; simp only [List.map_cons, List.map_nil, hd, k2]
      simp [show x1 ≠ x0 by nd, show x1 ≠ n0 by nd, show x1 ≠ y0 by nd, show n1 ≠ x0 by nd, show n1 ≠ n0 by nd,
        show n1 ≠ y0 by nd, h01, hn01]
    rw [hg1] at hs2
    have hy1 : y1 ∉ [x1, n1] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
    have k3 := comp_atv (σ := S2) hy1 v
    generalize applyF S2 (popOf [x1, n1], fun ch => if ch = y1 then [v] else []) = S3 at hs2 k3
    have hiy : y ∉ [y0, y1] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
    refine ⟨S3, 2, Run.cons _ hs1 (run_one hs2), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ch hch
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hch
      obtain ⟨c1, c2, c3, c4, c5⟩ := hch
      rw [k3, k2, fork_at hiy]
      simp only [List.mem_cons, List.not_mem_nil, or_false, c1, c2, c3, c4, c5, ite_false]
      by_cases e0 : ch = y0
      · subst e0; simp [show ch ≠ y1 by nd, nD ch c1 c2 c3 c4 c5]
      · by_cases e1 : ch = y1
        · subst e1; simp [e0, nD ch c1 c2 c3 c4 c5]
        · simp [e0, e1, nD ch c1 c2 c3 c4 c5]
    · rw [k3, k2]; simp [show y ≠ x1 by nd, show y ≠ n1 by nd, show y ≠ y1 by nd, show y ≠ x0 by nd,
        show y ≠ n0 by nd, show y ≠ y0 by nd, hy']
    · rw [k3, k3, k2, k2]
      simp [show x0 ≠ x1 by nd, show x0 ≠ n1 by nd, show x0 ≠ y1 by nd, show x0 ≠ n0 by nd, show x1 ≠ x0 by nd,
        show x1 ≠ n0 by nd, show x1 ≠ y0 by nd, h01, hx0]
    · rw [k3, k3, k2, k2]
      simp [show n0 ≠ x1 by nd, show n0 ≠ n1 by nd, show n0 ≠ y1 by nd, show n0 ≠ x0 by nd, show n1 ≠ x0 by nd,
        show n1 ≠ n0 by nd, show n1 ≠ y0 by nd, show n1 ≠ x1 by nd, hn01, hn0]
    · rw [k3, k3, k2, k2]
      simp [show x0 ≠ x1 by nd, show x0 ≠ n1 by nd, show x0 ≠ y1 by nd, show x0 ≠ n0 by nd,
        show n0 ≠ x1 by nd, show n0 ≠ n1 by nd, show n0 ≠ y1 by nd, show n0 ≠ x0 by nd, hx0, hn0]
      rw [hx0, hn0] at hlen; simp only [List.length_cons] at hlen; omega
    · simp only [k3, k2, fork_at hiy]
      simp [show x0 ≠ x1 by nd, show x0 ≠ n1 by nd, show x0 ≠ y1 by nd, show x0 ≠ n0 by nd,
        show n0 ≠ x1 by nd, show n0 ≠ n1 by nd, show n0 ≠ y1 by nd, show n0 ≠ x0 by nd, hx0, hn0, hv, evs]
  -- any other label: the same rule on both sides, reading none of the five
  cases hr : rs[l]? with
  | none => rw [step_graph_none hr] at hs; cases hs
  | some r =>
    have hr' := P.oth e1 e2 hr
    have hins := P.hins l r e1 e2 hr
    have hout := P.houts l r e1 e2 hr
    have hrd : ∀ ch ∈ r.insL, ch ∉ [y, x0, x1, n0, n1] := fun ch hc hm => by
      apply hins ch hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      rcases hm with h | h | h | h | h <;> simp [h]
    obtain ⟨fr, hf, rfl, hs'⟩ := outside_step hr hr' hrd hA hs
    have hf' : r.fire natVI σ' = some fr := by rw [fire_agree hA r hrd]; exact hf
    have keep : ∀ ch ∈ [y, x0, x1, n0, n1], applyF σ fr ch = σ ch ∧ applyF σ' fr ch = σ' ch := by
      intro ch hch
      have h1 : ch ∉ r.insL := nin_of hrd hch
      have h2 : ch ∉ r.outsL := fun ho => hout ch ho (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hch ⊢
        rcases hch with h | h | h | h | h <;> simp [h])
      exact ⟨by rw [applyF_app hf h1, fire_push0 hf h2, List.append_nil],
        by rw [applyF_app hf' h1, fire_push0 hf' h2, List.append_nil]⟩
    refine ⟨_, 1, run_one hs', applyF_agree hA fr, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(keep y (by simp)).2]; exact hy'
    · rw [(keep x1 (by simp)).2, (keep x0 (by simp)).2]; exact h01
    · rw [(keep n1 (by simp)).2, (keep n0 (by simp)).2]; exact hn01
    · rw [(keep x0 (by simp)).2, (keep n0 (by simp)).2]; exact hlen
    · rw [(keep y (by simp)).1, (keep x0 (by simp)).2, (keep n0 (by simp)).2]; exact hy

theorem fc2_fwd_term (P : PatFC2 rs rs' lc lf la lb x n y x0 x1 n0 n1 y0 y1 G) :
    ∀ σ σ', RelF2 y x0 x1 n0 n1 G σ σ' → Terminal (step (graph rs)) σ →
      ∃ t' m, Run (step (graph rs')) σ' m t' ∧ Terminal (step (graph rs')) t' ∧
        Agree [x, n, y, x0, x1, n0, n1] σ t' := by
  intro σ σ' ⟨hA, hy', h01, hn01, hlen, hy⟩ ht
  fdist P
  have L := P.labs
  have nD : ∀ ch, ch ≠ y → ch ≠ x0 → ch ≠ x1 → ch ≠ n0 → ch ≠ n1 → σ' ch = σ ch := fun ch a1 a2 a3 a4 a5 =>
    hA ch (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨a1, a2, a3, a4, a5⟩)
  -- `rs` terminal: the fork's input `y` is empty, so no pair waits in `rs'`; `x` or `n` is empty
  have hy0 : σ y = [] := fork_none_inv (step_none_inv P.hf (ht lf))
  have hX : σ' x0 = [] ∧ σ' n0 = [] := by
    rw [hy0] at hy
    rcases List.zipWith_eq_nil_iff.mp hy.symm with h | h
    · rw [h] at hlen; exact ⟨h, List.eq_nil_of_length_eq_zero (by rw [← hlen]; rfl)⟩
    · rw [h] at hlen; exact ⟨List.eq_nil_of_length_eq_zero hlen, h⟩
  have hxn : σ x = [] ∨ σ n = [] := by
    have h := step_none_inv P.hc (ht lc)
    cases hxv : σ x with
    | nil => exact Or.inl rfl
    | cons a as =>
      cases hnv : σ n with
      | nil => exact Or.inr rfl
      | cons b bs =>
        have hall : ∀ ch ∈ [x, n], σ ch ≠ [] := by
          intro ch hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · rw [hxv]; exact List.cons_ne_nil _ _
          · rw [hnv]; exact List.cons_ne_nil _ _
        rw [fire_comp hall] at h; cases h
  have hix : x ∉ [x0, x1] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
  have hin : n ∉ [n0, n1] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
  obtain ⟨m1, hr1⟩ := drain_fork P.hc' hix (σ' x) σ' rfl
  generalize hT1 : (fun c => if c = x then [] else if c ∈ [x0, x1] then σ' c ++ σ' x else σ' c) = T1 at hr1
  obtain ⟨m2, hr2⟩ := drain_fork P.hf' hin (T1 n) T1 rfl
  generalize hT2 : (fun c => if c = n then [] else if c ∈ [n0, n1] then T1 c ++ T1 n else T1 c) = T2 at hr2
  have k1 : ∀ c, T1 c = if c = x then [] else if c = x0 ∨ c = x1 then σ' c ++ σ' x else σ' c := by
    intro c; rw [← hT1]; simp
  have k2 : ∀ c, T2 c = if c = n then [] else if c = n0 ∨ c = n1 then T1 c ++ T1 n else T1 c := by
    intro c; rw [← hT2]; simp
  have sx : σ' x = σ x := nD x (by nd) (by nd) (by nd) (by nd) (by nd)
  have sn : σ' n = σ n := nD n (by nd) (by nd) (by nd) (by nd) (by nd)
  have t2x : T2 x = [] := by rw [k2, k1]; simp [show x ≠ n by nd, show x ≠ n0 by nd, show x ≠ n1 by nd]
  have t2n : T2 n = [] := by rw [k2]; simp
  have t2x0 : T2 x0 = σ x := by
    rw [k2, k1]; simp [show x0 ≠ n by nd, show x0 ≠ n0 by nd, show x0 ≠ n1 by nd, show x0 ≠ x by nd, hX.1, sx]
  have t2x1 : T2 x1 = σ x := by
    rw [k2, k1]; simp [show x1 ≠ n by nd, show x1 ≠ n0 by nd, show x1 ≠ n1 by nd, show x1 ≠ x by nd, h01, hX.1, sx]
  have t2n0 : T2 n0 = σ n := by
    rw [k2, k1, k1]; simp [show n0 ≠ n by nd, show n0 ≠ x by nd, show n0 ≠ x0 by nd, show n0 ≠ x1 by nd,
      show n ≠ x by nd, show n ≠ x0 by nd, show n ≠ x1 by nd, hX.2, sn]
  have t2n1 : T2 n1 = σ n := by
    rw [k2, k1, k1]; simp [show n1 ≠ n by nd, show n1 ≠ x by nd, show n1 ≠ x0 by nd, show n1 ≠ x1 by nd,
      show n ≠ x by nd, show n ≠ x0 by nd, show n ≠ x1 by nd, hn01, hX.2, sn]
  have hAg : Agree [x, n, y, x0, x1, n0, n1] σ T2 := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
    rw [k2, k1]; simp [c1, c2, c4, c5, c6, c7]; exact nD c c3 c4 c5 c6 c7
  refine ⟨T2, m1 + m2, run_trans hr1 hr2, fun l => ?_, hAg⟩
  by_cases e1 : l = lc
  · subst e1; exact step_none_of P.hc' (fire_fork_none t2x)
  by_cases e2 : l = lf
  · subst e2; exact step_none_of P.hf' (fire_fork_none t2n)
  by_cases e3 : l = la
  · subst e3; apply step_none_of P.ha'
    rcases hxn with h | h
    · exact fire_comp_none (c := x0) (by simp) (by rw [t2x0, h])
    · exact fire_comp_none (c := n0) (by simp) (by rw [t2n0, h])
  by_cases e4 : l = lb
  · subst e4; apply step_none_of P.hb'
    rcases hxn with h | h
    · exact fire_comp_none (c := x1) (by simp) (by rw [t2x1, h])
    · exact fire_comp_none (c := n1) (by simp) (by rw [t2n1, h])
  cases hr : rs[l]? with
  | none => exact step_graph_none (by rw [P.hsame l e1 e2 e3 e4]; exact hr) T2
  | some r => exact outside_none hr (P.oth e1 e2 hr) (P.hins l r e1 e2 hr) hAg (ht l)

theorem fc2_forward (P : PatFC2 rs rs' lc lf la lb x n y x0 x1 n0 n1 y0 y1 G) {σ0 t : Store Nat Nat} {k : Nat}
    (h0 : ∀ ch ∈ [y, x0, x1, n0, n1], σ0 ch = []) (hr : Run (step (graph rs)) σ0 k t)
    (ht : Terminal (step (graph rs)) t) :
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧
      Agree [x, n, y, x0, x1, n0, n1] t t' := by
  refine sim_complete (RelF2 y x0 x1 n0 n1 G) (Agree [x, n, y, x0, x1, n0, n1]) (fc2_fwd_step P) (fc2_fwd_term P)
    hr ht σ0 ⟨fun _ _ => rfl, h0 y (by simp), ?_, ?_, ?_, ?_⟩
  · rw [h0 x1 (by simp), h0 x0 (by simp)]
  · rw [h0 n1 (by simp), h0 n0 (by simp)]
  · rw [h0 x0 (by simp), h0 n0 (by simp)]
  · rw [h0 y (by simp), h0 x0 (by simp)]; rfl

/-! ## Backward: `rs` computes a pair when the first `rs'` copy does -/

def RelB2 (x n y x0 x1 n0 n1 y0 y1 : Nat) (G : E) (σ' σ : Store Nat Nat) : Prop :=
  Agree [x, n, y, x0, x1, n0, n1, y0, y1] σ' σ ∧ σ y = [] ∧
  ∃ A B Q0x Q0n Q1x Q1n : List Nat,
    σ x = A ++ σ' x ∧ σ n = B ++ σ' n ∧
    σ' x0 = Q0x ++ A ∧ σ' n0 = Q0n ++ B ∧ Q0x.length = Q0n.length ∧
    σ' x1 = Q1x ++ A ∧ σ' n1 = Q1n ++ B ∧ Q1x.length = Q1n.length ∧
    σ y0 = σ' y0 ++ List.zipWith (g2 G) Q0x Q0n ∧ σ y1 = σ' y1 ++ List.zipWith (g2 G) Q1x Q1n

theorem comp_none_inv {ins : List Nat} {o : Nat} {F : E} {σ : Store Nat Nat}
    (h : (Rule.comp ins o F).fire natVI σ = none) : ∃ c ∈ ins, σ c = [] := by
  by_cases hall : ∀ c ∈ ins, σ c ≠ []
  · rw [fire_comp hall] at h; cases h
  · exact exists_empty hall

/-- `rs` fires its comp on the fronts `a`, `b` of `x`, `n`, then its fork. -/
theorem fc2_pair (P : PatFC2 rs rs' lc lf la lb x n y x0 x1 n0 n1 y0 y1 G) {σ : Store Nat Nat} {a b : Nat}
    {as bs : List Nat} (ha : σ x = a :: as) (hb : σ n = b :: bs) (hy : σ y = []) :
    ∃ T, Run (step (graph rs)) σ 2 T ∧ ∀ ch, T ch =
      if ch = x then as else if ch = n then bs else if ch = y0 ∨ ch = y1 then σ ch ++ [g2 G a b] else σ ch := by
  fdist P
  have hall : ∀ ch ∈ [x, n], σ ch ≠ [] := by
    intro ch hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [ha]; exact List.cons_ne_nil _ _
    · rw [hb]; exact List.cons_ne_nil _ _
  have hs1 := step_of_fire P.hc (fire_comp hall)
  have hv : G.eval ([x, n].map (hd σ)) = g2 G a b := by simp [hd, ha, hb, g2]
  rw [hv] at hs1
  have hiy : y ∉ [x, n] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
  have k1 := comp_atv (σ := σ) hiy (g2 G a b)
  generalize applyF σ (popOf [x, n], fun ch => if ch = y then [g2 G a b] else []) = S at hs1 k1
  have hSy : S y = g2 G a b :: [] := by rw [k1]; simp [show y ≠ x by nd, show y ≠ n by nd, hy]
  have hs2 := step_of_fire P.hf (fire_fork (os := [y0, y1]) hSy)
  have hiy2 : y ∉ [y0, y1] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
  refine ⟨_, Run.cons _ hs1 (run_one hs2), fun ch => ?_⟩
  rw [fork_at hiy2, k1]
  by_cases ex : ch = x
  · subst ex; simp [show ch ≠ y by nd, show ch ≠ y0 by nd, show ch ≠ y1 by nd, ha]
  by_cases en : ch = n
  · subst en; simp [ex, show ch ≠ y by nd, show ch ≠ y0 by nd, show ch ≠ y1 by nd, hb]
  by_cases ey : ch = y
  · subst ey; simp [ex, en, show ch ≠ y0 by nd, show ch ≠ y1 by nd, hy]
  by_cases e0 : ch = y0
  · subst e0; simp [ex, en, ey]
  by_cases e1 : ch = y1
  · subst e1; simp [ex, en, ey, e0]
  simp [ex, en, ey, e0, e1]

theorem fc2_bwd_step (P : PatFC2 rs rs' lc lf la lb x n y x0 x1 n0 n1 y0 y1 G) :
    ∀ σ' σ l σ1', RelB2 x n y x0 x1 n0 n1 y0 y1 G σ' σ → step (graph rs') σ' l = some σ1' →
      ∃ σ1 k, Run (step (graph rs)) σ k σ1 ∧ RelB2 x n y x0 x1 n0 n1 y0 y1 G σ1' σ1 := by
  intro σ' σ l σ1' ⟨hA, hy, A, B, Q0x, Q0n, Q1x, Q1n, hx, hn, hx0, hn0, hl0, hx1, hn1, hl1, hy0, hy1⟩ hs
  fdist P
  have L := P.labs
  have nD : ∀ ch, ch ∉ [x, n, y, x0, x1, n0, n1, y0, y1] → σ ch = σ' ch := hA
  by_cases e1 : l = lc
  · subst e1
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.hc' hs
    obtain ⟨v, vs, hv, rfl⟩ := fork_inv hf
    have hix : x ∉ [x0, x1] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
    refine ⟨σ, 0, Run.refl _, ?_, hy, A ++ [v], B, Q0x, Q0n, Q1x, Q1n, ?_, ?_, ?_, ?_, hl0, ?_, ?_, hl1, ?_, ?_⟩
    · intro c hc; rw [fork_at hix]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
      simp [hc.1, hc.2.2.2.1, hc.2.2.2.2.1]; exact nD c (by simp [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
        hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2])
    · rw [fork_at hix, hx, hv]; simp
    · rw [fork_at hix, hn]; simp [show n ≠ x by nd, show n ≠ x0 by nd, show n ≠ x1 by nd]
    · rw [fork_at hix, hx0]; simp [show x0 ≠ x by nd]
    · rw [fork_at hix, hn0]; simp [show n0 ≠ x by nd, show n0 ≠ x0 by nd, show n0 ≠ x1 by nd]
    · rw [fork_at hix, hx1]; simp [show x1 ≠ x by nd]
    · rw [fork_at hix, hn1]; simp [show n1 ≠ x by nd, show n1 ≠ x0 by nd, show n1 ≠ x1 by nd]
    · rw [fork_at hix, hy0]; simp [show y0 ≠ x by nd, show y0 ≠ x0 by nd, show y0 ≠ x1 by nd]
    · rw [fork_at hix, hy1]; simp [show y1 ≠ x by nd, show y1 ≠ x0 by nd, show y1 ≠ x1 by nd]
  by_cases e2 : l = lf
  · subst e2
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.hf' hs
    obtain ⟨v, vs, hv, rfl⟩ := fork_inv hf
    have hin : n ∉ [n0, n1] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
    refine ⟨σ, 0, Run.refl _, ?_, hy, A, B ++ [v], Q0x, Q0n, Q1x, Q1n, ?_, ?_, ?_, ?_, hl0, ?_, ?_, hl1, ?_, ?_⟩
    · intro c hc; rw [fork_at hin]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
      simp [hc.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1]; exact nD c (by simp [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
        hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2])
    · rw [fork_at hin, hx]; simp [show x ≠ n by nd, show x ≠ n0 by nd, show x ≠ n1 by nd]
    · rw [fork_at hin, hn, hv]; simp
    · rw [fork_at hin, hx0]; simp [show x0 ≠ n by nd, show x0 ≠ n0 by nd, show x0 ≠ n1 by nd]
    · rw [fork_at hin, hn0]; simp [show n0 ≠ n by nd]
    · rw [fork_at hin, hx1]; simp [show x1 ≠ n by nd, show x1 ≠ n0 by nd, show x1 ≠ n1 by nd]
    · rw [fork_at hin, hn1]; simp [show n1 ≠ n by nd]
    · rw [fork_at hin, hy0]; simp [show y0 ≠ n by nd, show y0 ≠ n0 by nd, show y0 ≠ n1 by nd]
    · rw [fork_at hin, hy1]; simp [show y1 ≠ n by nd, show y1 ≠ n0 by nd, show y1 ≠ n1 by nd]
  by_cases ea : l = la
  · subst ea
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.ha' hs
    obtain ⟨hall, rfl⟩ := comp_inv hf
    obtain ⟨a, as, ha⟩ := cons_of_ne (hall x0 (by simp))
    obtain ⟨b, bs, hb⟩ := cons_of_ne (hall n0 (by simp))
    have hv : G.eval ([x0, n0].map (hd σ')) = g2 G a b := by simp [hd, ha, hb, g2]
    rw [hv]
    have ho : y0 ∉ [x0, n0] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
    have k := comp_atv (σ := σ') ho (g2 G a b)
    generalize applyF σ' (popOf [x0, n0], fun ch => if ch = y0 then [g2 G a b] else []) = S' at k
    have s'x : S' x0 = as := by rw [k]; simp [ha]
    have s'n : S' n0 = bs := by rw [k]; simp [hb]
    have s'y : S' y0 = σ' y0 ++ [g2 G a b] := by rw [k]; simp [show y0 ≠ x0 by nd, show y0 ≠ n0 by nd]
    have s'o : ∀ ch, ch ≠ x0 → ch ≠ n0 → ch ≠ y0 → S' ch = σ' ch := by
      intro ch c1 c2 c3; rw [k]; simp [c1, c2, c3]
    cases Q0x with
    | nil =>
      cases Q0n with
      | cons _ _ => simp at hl0
      | nil =>
        rw [List.nil_append] at hx0 hn0
        rw [hx0] at ha; rw [hn0] at hb
        subst ha; subst hb
        obtain ⟨T, hrun, hT⟩ := fc2_pair P (hx.trans (List.cons_append ..)) (hn.trans (List.cons_append ..)) hy
        refine ⟨T, 2, hrun, ?_, ?_, as, bs, ?_⟩
        · intro c hc
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
          obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hc
          rw [hT, s'o c (by nd) (by nd) (by nd)]
          simp only [c1, c2, c8, c9, false_or, or_false, ite_false]
          exact nD c (by simp [c1, c2, c3, c4, c5, c6, c7, c8, c9])
        · rw [hT]; simp [show y ≠ x by nd, show y ≠ n by nd, show y ≠ y0 by nd, show y ≠ y1 by nd, hy]
        · refine ⟨[], [], Q1x ++ [a], Q1n ++ [b], ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hT]; simp [show x ≠ n by nd, s'o x (by nd) (by nd) (by nd)]
          · rw [hT]; simp [show n ≠ x by nd, s'o n (by nd) (by nd) (by nd)]
          · rw [s'x]; rfl
          · rw [s'n]; rfl
          · rw [s'o x1 (by nd) (by nd) (by nd), hx1]; simp
          · rw [s'o n1 (by nd) (by nd) (by nd), hn1]; simp
          · simp [hl1]
          · rw [hT, s'y]; simp [show y0 ≠ x by nd, show y0 ≠ n by nd, hy0]
          · rw [hT, s'o y1 (by nd) (by nd) (by nd), hy1, zw_snoc hl1]
            simp [show y1 ≠ x by nd, show y1 ≠ n by nd]
    | cons a' Qx' =>
      cases Q0n with
      | nil => simp at hl0
      | cons b' Qn' =>
        rw [List.cons_append, ha] at hx0; rw [List.cons_append, hb] at hn0
        injection hx0 with ea eas; injection hn0 with eb ebs
        subst ea; subst eb
        refine ⟨σ, 0, Run.refl _, ?_, hy, A, B, ?_⟩
        · intro c hc
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
          obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hc
          rw [s'o c (by nd) (by nd) (by nd)]
          exact nD c (by simp [c1, c2, c3, c4, c5, c6, c7, c8, c9])
        · refine ⟨Qx', Qn', Q1x, Q1n, ?_, ?_, s'x.trans eas, s'n.trans ebs, ?_, ?_, ?_, hl1, ?_, ?_⟩
          · rw [s'o x (by nd) (by nd) (by nd)]; exact hx
          · rw [s'o n (by nd) (by nd) (by nd)]; exact hn
          · simp only [List.length_cons] at hl0; omega
          · rw [s'o x1 (by nd) (by nd) (by nd)]; exact hx1
          · rw [s'o n1 (by nd) (by nd) (by nd)]; exact hn1
          · rw [s'y, hy0]; simp [g2]
          · rw [s'o y1 (by nd) (by nd) (by nd)]; exact hy1
  by_cases eb : l = lb
  · subst eb
    obtain ⟨fr, hf, rfl⟩ := step_some_inv P.hb' hs
    obtain ⟨hall, rfl⟩ := comp_inv hf
    obtain ⟨a, as, ha⟩ := cons_of_ne (hall x1 (by simp))
    obtain ⟨b, bs, hb⟩ := cons_of_ne (hall n1 (by simp))
    have hv : G.eval ([x1, n1].map (hd σ')) = g2 G a b := by simp [hd, ha, hb, g2]
    rw [hv]
    have ho : y1 ∉ [x1, n1] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by nd, by nd⟩
    have k := comp_atv (σ := σ') ho (g2 G a b)
    generalize applyF σ' (popOf [x1, n1], fun ch => if ch = y1 then [g2 G a b] else []) = S' at k
    have s'x : S' x1 = as := by rw [k]; simp [ha]
    have s'n : S' n1 = bs := by rw [k]; simp [hb]
    have s'y : S' y1 = σ' y1 ++ [g2 G a b] := by rw [k]; simp [show y1 ≠ x1 by nd, show y1 ≠ n1 by nd]
    have s'o : ∀ ch, ch ≠ x1 → ch ≠ n1 → ch ≠ y1 → S' ch = σ' ch := by
      intro ch c1 c2 c3; rw [k]; simp [c1, c2, c3]
    cases Q1x with
    | nil =>
      cases Q1n with
      | cons _ _ => simp at hl1
      | nil =>
        rw [List.nil_append] at hx1 hn1
        rw [hx1] at ha; rw [hn1] at hb
        subst ha; subst hb
        obtain ⟨T, hrun, hT⟩ := fc2_pair P (hx.trans (List.cons_append ..)) (hn.trans (List.cons_append ..)) hy
        refine ⟨T, 2, hrun, ?_, ?_, as, bs, ?_⟩
        · intro c hc
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
          obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hc
          rw [hT, s'o c (by nd) (by nd) (by nd)]
          simp only [c1, c2, c8, c9, false_or, or_false, ite_false]
          exact nD c (by simp [c1, c2, c3, c4, c5, c6, c7, c8, c9])
        · rw [hT]; simp [show y ≠ x by nd, show y ≠ n by nd, show y ≠ y0 by nd, show y ≠ y1 by nd, hy]
        · refine ⟨Q0x ++ [a], Q0n ++ [b], [], [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
          · rw [hT]; simp [show x ≠ n by nd, s'o x (by nd) (by nd) (by nd)]
          · rw [hT]; simp [show n ≠ x by nd, s'o n (by nd) (by nd) (by nd)]
          · rw [s'o x0 (by nd) (by nd) (by nd), hx0]; simp
          · rw [s'o n0 (by nd) (by nd) (by nd), hn0]; simp
          · simp [hl0]
          · rw [s'x]; rfl
          · rw [s'n]; rfl
          · rw [hT, s'o y0 (by nd) (by nd) (by nd), hy0, zw_snoc hl0]
            simp [show y0 ≠ x by nd, show y0 ≠ n by nd]
          · rw [hT, s'y]; simp [show y1 ≠ x by nd, show y1 ≠ n by nd, hy1]
    | cons a' Qx' =>
      cases Q1n with
      | nil => simp at hl1
      | cons b' Qn' =>
        rw [List.cons_append, ha] at hx1; rw [List.cons_append, hb] at hn1
        injection hx1 with ea eas; injection hn1 with eb ebs
        subst ea; subst eb
        refine ⟨σ, 0, Run.refl _, ?_, hy, A, B, ?_⟩
        · intro c hc
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
          obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hc
          rw [s'o c (by nd) (by nd) (by nd)]
          exact nD c (by simp [c1, c2, c3, c4, c5, c6, c7, c8, c9])
        · refine ⟨Q0x, Q0n, Qx', Qn', ?_, ?_, ?_, ?_, hl0, s'x.trans eas, s'n.trans ebs, ?_, ?_, ?_⟩
          · rw [s'o x (by nd) (by nd) (by nd)]; exact hx
          · rw [s'o n (by nd) (by nd) (by nd)]; exact hn
          · rw [s'o x0 (by nd) (by nd) (by nd)]; exact hx0
          · rw [s'o n0 (by nd) (by nd) (by nd)]; exact hn0
          · simp only [List.length_cons] at hl1; omega
          · rw [s'o y0 (by nd) (by nd) (by nd)]; exact hy0
          · rw [s'y, hy1]; simp [g2]
  -- any other label: the same rule on both sides; `rs` may hold more on `y0`, `y1`
  cases hr' : rs'[l]? with
  | none => rw [step_graph_none hr'] at hs; cases hs
  | some r =>
    have hr : rs[l]? = some r := by rw [← P.hsame l e1 e2 ea eb]; exact hr'
    have hins := P.hins l r e1 e2 hr
    have hout := P.houts l r e1 e2 hr
    have hext : ∀ c ∈ r.insL, ∃ z, σ c = σ' c ++ z := by
      intro c hc
      by_cases c0 : c = y0
      · subst c0; exact ⟨_, hy0⟩
      by_cases c1 : c = y1
      · subst c1; exact ⟨_, hy1⟩
      refine ⟨[], ?_⟩; rw [List.append_nil]; apply nD c
      have := hins c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2, c0, c1⟩
    obtain ⟨fr, hf', hf, rfl, hs1⟩ := outside_step_ext hr hr' hext hs
    have nin : ∀ c ∈ [x, n, y, x0, x1, n0, n1], c ∉ r.insL := fun c hc h => hins c h hc
    have nout : ∀ c ∈ [y, x0, x1, n0, n1, y0, y1], c ∉ r.outsL := fun c hc h => hout c h hc
    have keep : ∀ c ∈ [y, x0, x1, n0, n1], applyF σ fr c = σ c ∧ applyF σ' fr c = σ' c := by
      intro c hc
      have h1 : c ∉ r.insL := nin c (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢; omega)
      have h2 : c ∉ r.outsL := nout c (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢; omega)
      exact ⟨by rw [applyF_app hf h1, fire_push0 hf h2, List.append_nil],
        by rw [applyF_app hf' h1, fire_push0 hf' h2, List.append_nil]⟩
    have app : ∀ c ∈ [x, n], applyF σ fr c = σ c ++ fr.2 c ∧ applyF σ' fr c = σ' c ++ fr.2 c := by
      intro c hc
      have h1 : c ∉ r.insL := nin c (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢; omega)
      exact ⟨applyF_app hf h1, applyF_app hf' h1⟩
    have drp : ∀ c ∈ [y0, y1], ∀ Z, σ c = σ' c ++ Z → applyF σ fr c = applyF σ' fr c ++ Z := by
      intro c hc Z hZ
      have h2 : c ∉ r.outsL := nout c (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢; omega)
      have hle : fr.1 c ≤ (σ' c).length := (r.node natVI).pop_le σ' fr c hf'
      rw [applyF_at, applyF_at, fire_push0 hf h2, hZ, drop_app_of_le hle]; simp
    refine ⟨_, 1, run_one hs1, applyF_agree hA fr, ?_, A, B, Q0x, Q0n, Q1x, Q1n, ?_, ?_, ?_, ?_, hl0, ?_, ?_, hl1,
      drp y0 (by simp) _ hy0, drp y1 (by simp) _ hy1⟩
    · rw [(keep y (by simp)).1]; exact hy
    · rw [(app x (by simp)).1, (app x (by simp)).2, hx, List.append_assoc]
    · rw [(app n (by simp)).1, (app n (by simp)).2, hn, List.append_assoc]
    · rw [(keep x0 (by simp)).2]; exact hx0
    · rw [(keep n0 (by simp)).2]; exact hn0
    · rw [(keep x1 (by simp)).2]; exact hx1
    · rw [(keep n1 (by simp)).2]; exact hn1

theorem fc2_bwd_term (P : PatFC2 rs rs' lc lf la lb x n y x0 x1 n0 n1 y0 y1 G) :
    ∀ σ' σ, RelB2 x n y x0 x1 n0 n1 y0 y1 G σ' σ → Terminal (step (graph rs')) σ' →
      ∃ t m, Run (step (graph rs)) σ m t ∧ Terminal (step (graph rs)) t ∧
        Agree [x, n, y, x0, x1, n0, n1] σ' t := by
  intro σ' σ ⟨hA, hy, A, B, Q0x, Q0n, Q1x, Q1n, hx, hn, hx0, hn0, hl0, hx1, hn1, hl1, hy0, hy1⟩ ht
  fdist P
  have L := P.labs
  have hσx : σ' x = [] := fork_none_inv (step_none_inv P.hc' (ht lc))
  have hσn : σ' n = [] := fork_none_inv (step_none_inv P.hf' (ht lf))
  have idle : ∀ (Qx Qn : List Nat), Qx.length = Qn.length → ((Qx ++ A) = [] ∨ (Qn ++ B) = []) →
      Qx = [] ∧ Qn = [] ∧ (A = [] ∨ B = []) := by
    intro Qx Qn hl h
    rcases h with h | h
    · obtain ⟨h1, h2⟩ := List.append_eq_nil_iff.mp h
      subst h1; exact ⟨rfl, List.eq_nil_of_length_eq_zero hl.symm, Or.inl h2⟩
    · obtain ⟨h1, h2⟩ := List.append_eq_nil_iff.mp h
      subst h1; exact ⟨List.eq_nil_of_length_eq_zero hl, rfl, Or.inr h2⟩
  have q0 : Q0x = [] ∧ Q0n = [] ∧ (A = [] ∨ B = []) := by
    apply idle Q0x Q0n hl0
    obtain ⟨c, hc, he⟩ := comp_none_inv (step_none_inv P.ha' (ht la))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · left; rw [← hx0]; exact he
    · right; rw [← hn0]; exact he
  have q1 : Q1x = [] ∧ Q1n = [] := by
    have := idle Q1x Q1n hl1 (by
      obtain ⟨c, hc, he⟩ := comp_none_inv (step_none_inv P.hb' (ht lb))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · left; rw [← hx1]; exact he
      · right; rw [← hn1]; exact he)
    exact ⟨this.1, this.2.1⟩
  have hAg : Agree [x, n, y, x0, x1, n0, n1] σ' σ := by
    intro c hc
    by_cases c0 : c = y0
    · subst c0; rw [hy0, q0.1, q0.2.1]; simp
    by_cases c1 : c = y1
    · subst c1; rw [hy1, q1.1, q1.2]; simp
    apply hA c
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc ⊢
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2, c0, c1⟩
  refine ⟨σ, 0, Run.refl _, fun l => ?_, hAg⟩
  by_cases e1 : l = lc
  · subst e1; apply step_none_of P.hc
    rcases q0.2.2 with h | h
    · exact fire_comp_none (c := x) (by simp) (by rw [hx, h, hσx]; rfl)
    · exact fire_comp_none (c := n) (by simp) (by rw [hn, h, hσn]; rfl)
  by_cases e2 : l = lf
  · subst e2; exact step_none_of P.hf (fire_fork_none hy)
  cases hr : rs[l]? with
  | none => exact step_graph_none hr σ
  | some r => exact outside_none (P.oth e1 e2 hr) hr (P.hins l r e1 e2 hr) hAg (ht l)

theorem fc2_backward (P : PatFC2 rs rs' lc lf la lb x n y x0 x1 n0 n1 y0 y1 G) {σ0 t' : Store Nat Nat} {k : Nat}
    (h0 : ∀ ch ∈ [y, x0, x1, n0, n1], σ0 ch = []) (hr : Run (step (graph rs')) σ0 k t')
    (ht : Terminal (step (graph rs')) t') :
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧
      Agree [x, n, y, x0, x1, n0, n1] t' t := by
  refine sim_complete (RelB2 x n y x0 x1 n0 n1 y0 y1 G) (fun σ' τ => Agree [x, n, y, x0, x1, n0, n1] σ' τ)
    (fc2_bwd_step P) (fc2_bwd_term P) hr ht σ0
    ⟨fun _ _ => rfl, h0 y (by simp), [], [], [], [], [], [], rfl, rfl, ?_, ?_, rfl, ?_, ?_, rfl, ?_, ?_⟩
  · rw [h0 x0 (by simp)]; rfl
  · rw [h0 n0 (by simp)]; rfl
  · rw [h0 x1 (by simp)]; rfl
  · rw [h0 n1 (by simp)]; rfl
  · simp
  · simp

end FC2

end Formal.Rewrite.Steps
