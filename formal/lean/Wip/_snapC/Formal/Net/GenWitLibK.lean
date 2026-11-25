import Formal.Net.GenWitLib

/-!
# Probe C-witgen (K): the event-list checker for O4b's `GenCellK` (compute joins N = 1..3)

O4's `GenCell` is `False` on a 3-input compute unit (`ipow_O4_vacuous`), so kernels with one
(ipow, collatz) are checked against O4b's `GenCellK`, which differs from `GenCell` only on
`.join` (`GenJoinK`: bd_join N = 1, 2, 3 -> `uor` -> request delay). `kChkGK` = `kChk` and the
internal-node checks of `xChk`, with the join check extended to N = 3 (the generated
bd_join_N3 LUT, `j3_gate`). `kChkGK_sound`: it implies `GenCellK`.
-/

namespace Formal.Net.CellBind.GenWit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Wit
open Formal.Net.CellBind Formal.Net.CellBind.Ops Formal.Net.CellBind.KOps Formal.Net.Ops.Gen

variable {n : Nat} (cd : Fin n → CD)

def joinXChkK (ins : List (Fin n)) (o : Fin n) (x : OX) : Bool :=
  (match ins with
   | [i0] => chainChk (cd i0).rq (cd o).rq x.sa x.ca
   | [i0, i1] =>
     (x.mm 0).all (fun e => bv (x.mm 0) (e + 1) == cel2 (rqv cd i0 e) (rqv cd i1 e) (bv (x.mm 0) e)) &&
     chainChk (x.mm 0) (cd o).rq x.sa x.ca
   | [i0, i1, i2] =>
     (x.mm 0).all (fun e => bv (x.mm 0) (e + 1) ==
       cel3 (rqv cd i0 e) (rqv cd i1 e) (rqv cd i2 e) (bv (x.mm 0) e)) &&
     chainChk (x.mm 0) (cd o).rq x.sa x.ca
   | _ => false) &&
  leafChk (ins.map fun i => (cd i).rq) (cd o).rq

def xChkK (x : OX) : K n → Bool
  | .join ins o _ _ _ => joinXChkK cd ins o x
  | k => xChk cd x k

def kChkGK (x : OX) (sv : Nat → Nat) (k : K n) : Bool := kChk cd sv k && xChkK cd x k

variable {cd}

theorem joinK_gsound {g : List Nat → Nat} {ins : List (Fin n)} {o : Fin n} {x : OX}
    (h1 : joinChk cd g ins o = true) (h2 : joinXChkK cd ins o x = true) :
    GenJoinK g (ins.map (wch cd)) (wch cd o) := by
  have J := join_sound h1
  simp only [joinXChkK, Bool.and_eq_true] at h2
  obtain ⟨hn, hl⟩ := h2
  refine ⟨?_, by rw [map_req]; exact leaf_sound hl, J.wire, J.dat, J.initO, J.initI⟩
  match ins, hn with
  | [i0], hn => exact ⟨(wch cd i0).req, rfl, chain_sound hn, by simp only [wch, CD.ch, bv_zero]⟩
  | [i0, i1], hn =>
    simp only [Bool.and_eq_true] at hn
    exact ⟨bv (x.mm 0), cnode_of (G := fun p q => cel2 p.1 p.2 q) j2_gate hn.1, chain_sound hn.2,
      by simp only [wch, CD.ch, bv_zero]⟩
  | [i0, i1, i2], hn =>
    simp only [Bool.and_eq_true] at hn
    exact ⟨bv (x.mm 0), cnode_of (G := fun p q => cel3 p.1 p.2.1 p.2.2 q) j3_gate hn.1, chain_sound hn.2,
      by simp only [wch, CD.ch, bv_zero]⟩
  | [], hn => simp at hn
  | _ :: _ :: _ :: _ :: _, hn => simp at hn

/-- **The checker is sound for `GenCellK`.** -/
theorem kChkGK_sound (x : OX) (sv : Nat → Nat) (k : K n) (h : kChkGK cd x sv k = true) :
    GenCellK (wch cd) sv k := by
  simp only [kChkGK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  cases k with
  | join ins o e js _ => exact joinK_gsound h1 h2
  | _ =>
    unfold GenCellK
    exact kChkG_sound x sv _ (by simp only [kChkG, Bool.and_eq_true]; exact ⟨h1, h2⟩)

end Formal.Net.CellBind.GenWit
