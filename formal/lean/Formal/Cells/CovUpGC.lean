import Formal.Cells.CovUpDec
import Formal.Cells.UnionUpDec

/-!
# Formal.Cells.CovUpGC — the claim hypothesis `hGC` of `CovUpMain.timedA_follows_cu` as one Boolean (shard B)

## Problem, plainly
`timedA_follows_cu` asks of every data-gate claim: it is gate-proved (`GateProofU`), or it is a chain (`ChainUpOK`) of
gate-proved claims of the list. A generated certificate gives, per claim, a hint: the covers of its pins (`gp`), or the
indices of its chain's segments (`ch`). `hgcB` checks all of it over C's Sep/Up tables (`AO.sepL`, `AO.upL`);
`hgc_of_B` turns `hgcB … = true` into exactly the `hGC` hypothesis.

## Proved (core Lean)
`hgc_of_B` (pins of every gate duplicate-free assumed, as C's `valOK_of_B` needs). Not shown: any instance.
-/

namespace Formal.Cells.CovUpGC
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedDecX
  Formal.Net.AO Formal.Cells.UnionUp Formal.Cells.UnionUpDec Formal.Cells.CovUp Formal.Cells.CovUpDec

variable {α : Type} [DecidableEq α]

inductive GHint (α : Type) where
  | gp (covL : List (α × Cov))
  | ch (ids : List Nat)

def covOf (covL : List (α × Cov)) (u : α) : Cov :=
  ((covL.find? fun p => p.1 == u).map (·.2)).getD .X

section
variable (N : TNet α) (dat : α → Bool) (sl : List (α × Nat × α × Nat × Nat))
  (ul : List ((α × Nat) × (α × Nat) × Nat)) (s0 : α → Bool) (cl : List (Claim α)) (hs : List (GHint α))

/-- Claim `j` is gate-proved by its hint. -/
def gpOK (j : Nat) : Bool :=
  match hs[j]?, cl[j]? with
  | some (.gp covL), some c => gateProofUB N dat (sepL sl) (upL ul) s0 cl c (covOf covL)
  | _, _ => false

def hgcB : Bool :=
  (List.range cl.length).all fun i => match cl[i]? with
    | none => true
    | some c => !N.gate c.z || (match hs[i]? with
      | some (.gp covL) => gateProofUB N dat (sepL sl) (upL ul) s0 cl c (covOf covL)
      | some (.ch ids) => ids.all (gpOK N dat sl ul s0 cl hs) && chainUpB sl ul c (ids.filterMap fun j => cl[j]?)
      | none => false)

theorem gp_of_gpOK (hnd : ∀ v, (N.pins v).Nodup) {j : Nat} (h : gpOK N dat sl ul s0 cl hs j = true) :
    ∃ c, cl[j]? = some c ∧ GateProofU N dat (sepL sl) (upL ul) s0 cl c := by
  unfold gpOK at h
  cases hh : hs[j]? with
  | none => rw [hh] at h; cases h
  | some g =>
    cases g with
    | ch _ => rw [hh] at h; cases h
    | gp covL =>
      cases hc : cl[j]? with
      | none => rw [hh, hc] at h; cases h
      | some c =>
        rw [hh, hc] at h
        exact ⟨c, rfl, gateProofU_of_B N dat _ _ s0 cl c _ (hnd c.z) h⟩

theorem hgc_of_B (hnd : ∀ v, (N.pins v).Nodup) (h : hgcB N dat sl ul s0 cl hs = true) :
    ∀ c ∈ cl, N.gate c.z = true → GateProofU N dat (sepL sl) (upL ul) s0 cl c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ cl ∧ GateProofU N dat (sepL sl) (upL ul) s0 cl c') ∧
        ChainUpOK (sepL sl) (upL ul) c cs := by
  intro c hc hg
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc
  have hall := List.all_eq_true.1 h i (List.mem_range.2 hi)
  have hci' : cl[i]? = some c := by rw [List.getElem?_eq_getElem hi, hci]
  rw [hci'] at hall
  simp only [hg, Bool.not_true, Bool.false_or] at hall
  cases hh : hs[i]? with
  | none => rw [hh] at hall; cases hall
  | some g =>
    rw [hh] at hall
    cases g with
    | gp covL => exact Or.inl (gateProofU_of_B N dat _ _ s0 cl c _ (hnd c.z) hall)
    | ch ids =>
      simp only [Bool.and_eq_true, List.all_eq_true] at hall
      obtain ⟨hids, hch⟩ := hall
      refine Or.inr ⟨_, fun c' hc' => ?_, chainUpB_sound sl ul _ c hch⟩
      obtain ⟨j, hj, hcj⟩ := List.mem_filterMap.1 hc'
      obtain ⟨c'', hc'', hgp⟩ := gp_of_gpOK N dat sl ul s0 cl hs hnd (hids j hj)
      rw [hcj] at hc''
      cases hc''
      exact ⟨List.mem_of_getElem? hcj, hgp⟩

end

end Formal.Cells.CovUpGC
