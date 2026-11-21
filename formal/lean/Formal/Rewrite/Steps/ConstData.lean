import Formal.Rewrite.Steps.Dedupe
import Formal.Rewrite.Steps.Absorb

/-!
# Formal.Rewrite.Steps.ConstData — a comp reads a channel that only carries a constant as that constant (shard A, 2026-11-19)

**Problem, plainly.** bdc's `BDC_CONST_DATA` (on under `BDC_AUTO=1`): a fused region reads an operand whose value is
a known constant (a constant's result, or a fork of one) as a literal, while the channel and its handshake stay. Is
that the same, whatever surrounds it?

**Proved** (`cd_forward`, `cd_backward`): for ANY imported graph `rs` holding `comp ins y F` at `lc`, a channel class
`C` containing `ins[i]` whose every writer (in `rs`) is a constant comp `comp _ c (lit v)` or a fork of a channel of
`C`, `y ∉ C`, and `rs'` equal except `comp ins y (constE |ins| i v F)` at `lc` (input `i` replaced by the literal
`v`): from any store with the channels of `C` empty, the two graphs have the same complete runs, with the same stores
(`Lockstep` with equal stores and the invariant "every token on `C` is `v`").

**Not covered:** token level only.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

/-- `F` with input `i` replaced by the literal `v` (inputs `0 .. n-1`). -/
def constE (n i v : Nat) (F : E) : E :=
  F.subst ((List.range n).map fun j => if j = i then .lit v else .var j)

theorem eval_constE {n i v : Nat} (F : E) {vs : List Nat} (hl : vs.length = n) (hi : i < n) (hv : vs.getD i 0 = v) :
    (constE n i v F).eval vs = F.eval vs := by
  simp only [constE, eval_subst, List.map_map]
  congr 1
  rw [← hl]
  conv => rhs; rw [← range_getD vs]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp]
  by_cases e : j = i
  · subst e; simp only [ite_true, E.eval]; rw [← hv, List.getD_eq_getElem?_getD]
  · simp [e, E.eval]

/-- Every writer of a channel of `C` is a constant comp of value `v` or a fork of a channel of `C`. -/
def ConstWriter (C : List Nat) (v : Nat) (r : Rule) : Prop :=
  ∀ c ∈ C, c ∈ r.outsL → (∃ ins', r = .comp ins' c (.lit v)) ∨ (∃ k os, r = .fork k os ∧ k ∈ C)

def InvC (C : List Nat) (v : Nat) (σ : Store Nat Nat) : Prop := ∀ c ∈ C, ∀ t ∈ σ c, t = v

theorem invC_step {C : List Nat} {v : Nat} {r : Rule} (hw : ConstWriter C v r) {σ : Store Nat Nat} {fr : Fire Nat Nat}
    (hinv : InvC C v σ) (hf : r.fire natVI σ = some fr) : InvC C v (applyF σ fr) := by
  intro c hc t ht
  rw [applyF_at] at ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hinv c hc t (List.mem_of_mem_drop ht)
  · by_cases ho : c ∈ r.outsL
    · rcases hw c hc ho with ⟨ins', rfl⟩ | ⟨k, os, rfl, hk⟩
      · by_cases hall : ∀ d ∈ ins', σ d ≠ []
        · rw [fire_comp hall] at hf
          obtain rfl := (Option.some.inj hf).symm
          simp only [ite_true, List.mem_singleton] at ht; rw [ht]; rfl
        · obtain ⟨d, hd, he⟩ := exists_empty hall
          rw [fire_comp_none hd he] at hf; cases hf
      · cases hk' : σ k with
        | nil => rw [fire_fork_none hk'] at hf; cases hf
        | cons w ws =>
          rw [fire_fork hk'] at hf
          obtain rfl := (Option.some.inj hf).symm
          have hco : c ∈ os := by simpa [Rule.outsL] using ho
          simp only [hco, ite_true, List.mem_singleton] at ht
          rw [ht]; exact hinv k hk w (by rw [hk']; simp)
    · rw [fire_push0 hf ho] at ht; cases ht

structure PatCD (rs rs' : List Rule) (lc y i v : Nat) (ins C : List Nat) (F : E) : Prop where
  hc : rs[lc]? = some (.comp ins y F)
  hc' : rs'[lc]? = some (.comp ins y (constE ins.length i v F))
  hsame : ∀ l, l ≠ lc → rs'[l]? = rs[l]?
  hi : i < ins.length
  hC : ins.getD i 0 ∈ C
  hw : ∀ (l : Nat) (r : Rule), rs[l]? = some r → ConstWriter C v r
  hy : y ∉ C

section CD
variable {rs rs' : List Rule} {lc y i v : Nat} {ins C : List Nat} {F : E}

theorem PatCD.hw' (P : PatCD rs rs' lc y i v ins C F) :
    ∀ (l : Nat) (r : Rule), rs'[l]? = some r → ConstWriter C v r := by
  intro l r hr
  by_cases e : l = lc
  · subst e; rw [P.hc'] at hr; obtain rfl := Option.some.inj hr
    intro c hc ho; simp [Rule.outsL] at ho; subst ho; exact absurd hc P.hy
  · rw [P.hsame l e] at hr; exact P.hw l r hr

theorem cd_fire (P : PatCD rs rs' lc y i v ins C F) {σ : Store Nat Nat} (hinv : InvC C v σ) :
    (Rule.comp ins y (constE ins.length i v F)).fire natVI σ = (Rule.comp ins y F).fire natVI σ := by
  by_cases hall : ∀ c ∈ ins, σ c ≠ []
  · rw [fire_comp hall, fire_comp hall]
    have hv : (ins.map (hd σ)).getD i 0 = v := by
      have hmem : ins.getD i 0 ∈ ins := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem P.hi]; exact List.getElem_mem P.hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem P.hi]
      simp only [Option.map_some, Option.getD_some]
      have e : ins[i]'P.hi = ins.getD i 0 := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem P.hi]; rfl
      rw [e]
      have hne := hall _ hmem
      cases h : σ (ins.getD i 0) with
      | nil => exact absurd h hne
      | cons t ts => simp only [hd, h, List.headD_cons]; exact hinv _ P.hC t (by rw [h]; simp)
    rw [eval_constE F (by simp) P.hi hv]
  · obtain ⟨c, hc, he⟩ := exists_empty hall
    rw [fire_comp_none hc he, fire_comp_none hc he]

theorem cd_lockstep (P : PatCD rs rs' lc y i v ins C F) :
    Lockstep rs rs' (fun σ σ' => σ' = σ ∧ InvC C v σ) := by
  intro σ σ' l hR
  obtain ⟨he, hinv⟩ := hR
  rw [he]
  have hst : step (graph rs') σ l = step (graph rs) σ l := by
    by_cases e : l = lc
    · subst e; rw [step_graph P.hc, step_graph P.hc', cd_fire P hinv]
    · simp only [step, graph, graphV, P.hsame l e]
  rw [hst]
  have pres : ∀ u, step (graph rs) σ l = some u → InvC C v u := by
    intro u hu
    cases hr : rs[l]? with
    | none => rw [none_none hr] at hu; cases hu
    | some r =>
      rw [step_graph hr] at hu
      cases hf : r.fire natVI σ with
      | none => rw [hf] at hu; cases hu
      | some fr => rw [hf] at hu; rw [← Option.some.inj hu]; exact invC_step (P.hw l r hr) hinv hf
  exact ⟨Iff.rfl, fun u hu => ⟨u, hu, rfl, pres u hu⟩, fun u hu => ⟨u, hu, rfl, pres u hu⟩⟩

theorem invC_init {σ0 : Store Nat Nat} (h0 : ∀ c ∈ C, σ0 c = []) : InvC C v σ0 := by
  intro c hc t ht; rw [h0 c hc] at ht; cases ht

theorem cd_forward (P : PatCD rs rs' lc y i v ins C F) {σ0 t : Store Nat Nat} {n : Nat}
    (h0 : ∀ c ∈ C, σ0 c = []) (hr : Run (step (graph rs)) σ0 n t) (ht : Terminal (step (graph rs)) t) :
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧ Agree [] t t' := by
  obtain ⟨t', hr', hR⟩ := lockstep_fwd (cd_lockstep P) hr σ0 ⟨rfl, invC_init h0⟩
  exact ⟨t', n, hr', (lockstep_term (cd_lockstep P) hR).mp ht, fun c _ => hR.1 ▸ rfl⟩

theorem cd_backward (P : PatCD rs rs' lc y i v ins C F) {σ0 t' : Store Nat Nat} {n : Nat}
    (h0 : ∀ c ∈ C, σ0 c = []) (hr : Run (step (graph rs')) σ0 n t') (ht : Terminal (step (graph rs')) t') :
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧ Agree [] t' t := by
  obtain ⟨t, hr0, hR⟩ := lockstep_bwd (cd_lockstep P) hr σ0 ⟨rfl, invC_init h0⟩
  exact ⟨t, n, hr0, (lockstep_term (cd_lockstep P) hR).mpr ht, fun c _ => hR.1 ▸ rfl⟩

end CD

end Formal.Rewrite.Steps
