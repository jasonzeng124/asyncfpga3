import Formal.Net.CapstoneNet

/-!
# Probe C-8m: kernel checks of the generated gcd_hw circuit network

* `ops_ok`: every operator passes `OpChk` against `GcdHw.Gcd.rules` and the descriptors;
* `rank_ok`: the descriptor graph is ranked;
* `prod_ok`, `cons_ok`: every channel has exactly one producer and one consumer (the `Net`
  axioms);
* `out0_desc`: the environment's `out0` channel carries GcdHw channel 250 (`out0`).
-/

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.CapNet Formal.Net.GcdHw

set_option maxRecDepth 100000

def opAt (o : Fin NO) : K NC := ops.getD o.val (K.sink 0)
def prodOf (c : Fin NC) : Fin NO := prodT.getD c.val 0
def consOf (c : Fin NC) : Fin NO := consT.getD c.val 0

theorem ops_len : ops.length = NO := by decide +kernel

theorem ops_all1 : (ops.take 120).all (fun k => decide (OpChk tab k)) = true := by decide +kernel
theorem ops_all2 : ((ops.drop 120).take 120).all (fun k => decide (OpChk tab k)) = true := by decide +kernel
theorem ops_all3 : ((ops.drop 120).drop 120).all (fun k => decide (OpChk tab k)) = true := by decide +kernel

theorem ops_all : ops.all (fun k => decide (OpChk tab k)) = true := by
  rw [← List.take_append_drop 120 ops, List.all_append, ops_all1, ← List.take_append_drop 120 (ops.drop 120),
    List.all_append, ops_all2, ops_all3]; rfl

theorem getD_mem {o : Fin NO} : opAt o ∈ ops := by
  unfold opAt
  have h : o.val < ops.length := by rw [ops_len]; exact o.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem ops_ok (o : Fin NO) : OpChk tab (opAt o) :=
  of_decide_eq_true (List.all_eq_true.mp ops_all _ getD_mem)

theorem rank_chk : (List.range tab.desc.length).all (fun c => decide ((tab.d c).deps ≠ [] →
    tab.rk c + 1 < tab.nf ∧ ∀ c' ∈ (tab.d c).deps, tab.rk c' < tab.rk c)) = true := by decide +kernel

theorem rank_ok : RankOK tab := by
  intro c hd
  by_cases h : c < tab.desc.length
  · exact of_decide_eq_true (List.all_eq_true.mp rank_chk c (List.mem_range.mpr h)) hd
  · exfalso; apply hd
    have : tab.d c = .zero := by
      simp only [Tab.d]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [this]; rfl

theorem nf_pos : 0 < tab.nf := by decide

theorem prod_chk : (List.range NO).all (fun o => (ops.getD o (K.sink 0)).outsC.all
    (fun c => (prodT.getD c.val 0).val == o)) = true := by decide +kernel
theorem cons_chk : (List.range NO).all (fun o => (ops.getD o (K.sink 0)).insC.all
    (fun c => (consT.getD c.val 0).val == o)) = true := by decide +kernel
theorem prodm_chk : (List.range NC).all (fun c =>
    ((ops.getD (prodT.getD c 0).val (K.sink 0)).outsC.map Fin.val).contains c) = true := by decide +kernel
theorem consm_chk : (List.range NC).all (fun c =>
    ((ops.getD (consT.getD c 0).val (K.sink 0)).insC.map Fin.val).contains c) = true := by decide +kernel

theorem prod_out (o : Fin NO) (c : Fin NC) (h : c ∈ (opAt o).outsC) : prodOf c = o := by
  have := List.all_eq_true.mp (List.all_eq_true.mp prod_chk o.val (List.mem_range.mpr o.isLt)) c h
  exact Fin.ext (by simpa [prodOf] using this)

theorem cons_in (o : Fin NO) (c : Fin NC) (h : c ∈ (opAt o).insC) : consOf c = o := by
  have := List.all_eq_true.mp (List.all_eq_true.mp cons_chk o.val (List.mem_range.mpr o.isLt)) c h
  exact Fin.ext (by simpa [consOf] using this)

theorem prod_mem (c : Fin NC) : c ∈ (opAt (prodOf c)).outsC := by
  have := List.all_eq_true.mp prodm_chk c.val (List.mem_range.mpr c.isLt)
  simp only [List.contains_iff_mem, List.mem_map] at this
  obtain ⟨c', h1, h2⟩ := this
  have : c' = c := Fin.ext h2
  subst this; exact h1

theorem cons_mem (c : Fin NC) : c ∈ (opAt (consOf c)).insC := by
  have := List.all_eq_true.mp consm_chk c.val (List.mem_range.mpr c.isLt)
  simp only [List.contains_iff_mem, List.mem_map] at this
  obtain ⟨c', h1, h2⟩ := this
  have : c' = c := Fin.ext h2
  subst this; exact h1

/-- The network (Ops `Net`). -/
def net : Ops.Net (Fin NC) (Fin NO) where
  ins o := (opAt o).insC
  outs o := (opAt o).outsC
  prod := prodOf
  cons := consOf
  prod_iff c o := ⟨fun h => prod_out o c h, fun h => h ▸ prod_mem c⟩
  cons_iff c o := ⟨fun h => cons_in o c h, fun h => h ▸ cons_mem c⟩

theorem out0_desc : tab.d out0.val = .hist 250 0 := by decide

end Formal.Net.CapNet.Gcd
