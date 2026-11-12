import Formal.Net.KernelCapDefs

/-!
# Probe C-8y2: the network obligations of `KP` from Boolean checks

For a new kernel, the network-shaped obligations of `KP` (`ops_ok`, `rank_ok`, `prod_out`,
`cons_in`, `prod_mem`, `cons_mem`, `spok`, `noloop`, `env_np`) follow from Boolean checks on the
generated lists, each discharged by `decide +kernel` (C-8m's NetChk and C-8r's CutSpine proofs,
stated once over `[KD]`). gcd_hw and ipow reuse their existing theorems instead.
-/

namespace Formal.Net.KCap
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open KD

variable [KD]

theorem getD_mem_of (hl : ops.length = NO) {o : Fin NO} : opAt o ∈ ops := by
  unfold opAt
  have h : o.val < ops.length := by rw [hl]; exact o.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem ops_ok_of (hl : ops.length = NO) (h : ops.all (fun k => decide (OpChk tab k)) = true)
    (o : Fin NO) : OpChk tab (opAt o) :=
  of_decide_eq_true (List.all_eq_true.mp h _ (getD_mem_of hl))

theorem spok_of (hl : ops.length = NO) (h : ops.all SpOK = true) (o : Fin NO) : SpOK (opAt o) = true :=
  List.all_eq_true.mp h _ (getD_mem_of hl)

theorem rank_ok_of (h : (List.range tab.desc.length).all (fun c => decide ((tab.d c).deps ≠ [] →
    tab.rk c + 1 < tab.nf ∧ ∀ c' ∈ (tab.d c).deps, tab.rk c' < tab.rk c)) = true) : RankOK tab := by
  intro c hd
  by_cases hc : c < tab.desc.length
  · exact of_decide_eq_true (List.all_eq_true.mp h c (List.mem_range.mpr hc)) hd
  · exfalso; apply hd
    have : tab.d c = .zero := by
      simp only [Tab.d]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [this]; rfl

theorem prod_out_of (h : (List.range NO).all (fun o => (ops.getD o (K.sink 0)).outsC.all
    (fun c => (prodT.getD c.val 0).val == o)) = true)
    (o : Fin NO) (c : Fin NC) (hc : c ∈ (opAt o).outsC) : prodOf c = o := by
  have := List.all_eq_true.mp (List.all_eq_true.mp h o.val (List.mem_range.mpr o.isLt)) c hc
  exact Fin.ext (by simpa [prodOf] using this)

theorem cons_in_of (h : (List.range NO).all (fun o => (ops.getD o (K.sink 0)).insC.all
    (fun c => (consT.getD c.val 0).val == o)) = true)
    (o : Fin NO) (c : Fin NC) (hc : c ∈ (opAt o).insC) : consOf c = o := by
  have := List.all_eq_true.mp (List.all_eq_true.mp h o.val (List.mem_range.mpr o.isLt)) c hc
  exact Fin.ext (by simpa [consOf] using this)

theorem prod_mem_of (h : (List.range NC).all (fun c =>
    ((ops.getD (prodT.getD c 0).val (K.sink 0)).outsC.map Fin.val).contains c) = true)
    (c : Fin NC) : c ∈ (opAt (prodOf c)).outsC := by
  have := List.all_eq_true.mp h c.val (List.mem_range.mpr c.isLt)
  simp only [List.contains_iff_mem, List.mem_map] at this
  obtain ⟨c', h1, h2⟩ := this
  have : c' = c := Fin.ext h2
  subst this; exact h1

theorem cons_mem_of (h : (List.range NC).all (fun c =>
    ((ops.getD (consT.getD c 0).val (K.sink 0)).insC.map Fin.val).contains c) = true)
    (c : Fin NC) : c ∈ (opAt (consOf c)).insC := by
  have := List.all_eq_true.mp h c.val (List.mem_range.mpr c.isLt)
  simp only [List.contains_iff_mem, List.mem_map] at this
  obtain ⟨c', h1, h2⟩ := this
  have : c' = c := Fin.ext h2
  subst this; exact h1

theorem noloop_of (h : (List.range NC).all (fun c => prodT.getD c 0 != consT.getD c 0) = true)
    (c : Fin NC) : prodOf c ≠ consOf c := by
  have := List.all_eq_true.mp h c.val (List.mem_range.mpr c.isLt)
  intro e
  simp only [prodOf, consOf] at e
  rw [e] at this; simp at this

theorem env_np_of (h : (List.range nIn).all (fun w => !produced w) = true) (w : Nat) (hw : w < nIn) :
    produced w = false := by
  have := List.all_eq_true.mp h w (List.mem_range.mpr hw)
  simpa using this

end Formal.Net.KCap
