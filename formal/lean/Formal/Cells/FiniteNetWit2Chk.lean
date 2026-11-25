import Formal.Cells.FiniteNetWit2Data

/-!
# Probe Bfin3 (shard B): the kernel checks of the gate-modelled node traces on `chW`

Note: `formal/notes/B-finite-net-wit2.md`. For every operator of gcd_hw: the fork acknowledge
C-element (N ≤ 4), the 2-input join request C-element, both steer branches and the steer
acknowledge OR, each against its checker (`FiniteNetWit2Lib`) on C's channel traces `cdA`
and the generated node lists (`FiniteNetWit2Data`); plus sortedness of every list.
`decide +kernel` only. Core Lean only.
-/

namespace Formal.Cells.FiniteNetWit2
open Formal.Cells
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Wit (CD cdA nv)
open Formal.Net.Ops.Gen (cel2 cel3)
open Formal.Cells.AssumeGuaranteeEnds (cel4)
open Formal.Cells.AssumeGuaranteeEndsCap (forkOuts joinIns d0)
open Formal.Cells.FiniteRunsWit (sortedB bndD)

def Gf2 (p : Fin 2 → Bool) (q : Bool) : Bool := cel2 (p 0) (p 1) q
def Gf3 (p : Fin 3 → Bool) (q : Bool) : Bool := cel3 (p 0) (p 1) (p 2) q
def Gf4 (p : Fin 4 → Bool) (q : Bool) : Bool := cel4 (p 0) (p 1) (p 2) (p 3) q

/-- A steer's (input, true output, false output). -/
def stTF : K NC → Option (Fin NC × Fin NC × Fin NC)
  | .steerC j t f => some (j, t, f)
  | .steerD j t f _ _ => some (j, t, f)
  | _ => none

/-- The select of a steer on channel `j`: bit 0 of its bus. -/
def selS (j : Fin NC) (t : Nat) : Bool := nv (cdA j).d0 (cdA j).dt t % 2 == 1

def celChk (sel : CD → List Nat) (cs : List (Fin NC)) (Ln : List Nat) : Bool :=
  if cs.length = 2 then celB Gf2 (fun i : Fin 2 => sel (cdA (cs.getD i.val d0))) Ln
  else if cs.length = 3 then celB Gf3 (fun i : Fin 3 => sel (cdA (cs.getD i.val d0))) Ln
  else if cs.length = 4 then celB Gf4 (fun i : Fin 4 => sel (cdA (cs.getD i.val d0))) Ln
  else true

def faChk (o : Fin NO) : Bool :=
  match forkOuts (opAt o) with
  | some os => celChk CD.ak os (faL.getD o.val [])
  | none => true

def jrChk (o : Fin NO) : Bool :=
  match joinIns (opAt o) with
  | some ins => if ins.length = 2 then celChk CD.rq ins (jrL.getD o.val []) else true
  | none => true

def stChk (o : Fin NO) : Bool :=
  match stTF (opAt o) with
  | some (j, t, f) =>
    stB true (cdA j).rq (selS j) (tabL.getD o.val []) (sbTL.getD o.val []) &&
    stB false (cdA j).rq (selS j) (tabL.getD o.val []) (sbFL.getD o.val []) &&
    orB (tabL.getD o.val []) (cdA f).ak (cdA t).ak (aoL.getD o.val []) && bndD (cdA j).dt
  | none => true

def srtChk (o : Fin NO) : Bool :=
  sortedB (faL.getD o.val []) && sortedB (jrL.getD o.val []) && sortedB (sbTL.getD o.val []) &&
  sortedB (sbFL.getD o.val []) && sortedB (aoL.getD o.val [])

def opChk (n : Nat) : Bool :=
  if h : n < NO then faChk ⟨n, h⟩ && jrChk ⟨n, h⟩ && stChk ⟨n, h⟩ && srtChk ⟨n, h⟩ else true

def chChk (n : Nat) : Bool :=
  if h : n < NC then sortedB (cdA ⟨n, h⟩).rq && sortedB (cdA ⟨n, h⟩).ak else true

set_option maxRecDepth 100000

theorem op_c1 : (List.range' 0 60).all opChk = true := by decide +kernel
theorem op_c2 : (List.range' 60 60).all opChk = true := by decide +kernel
theorem op_c3 : (List.range' 120 60).all opChk = true := by decide +kernel
theorem op_c4 : (List.range' 180 60).all opChk = true := by decide +kernel
theorem op_c5 : (List.range' 240 60).all opChk = true := by decide +kernel
theorem op_c6 : (List.range' 300 67).all opChk = true := by decide +kernel
theorem ch_c1 : (List.range' 0 240).all chChk = true := by decide +kernel
theorem ch_c2 : (List.range' 240 225).all chChk = true := by decide +kernel

theorem range'_all {f : Nat → Bool} {a n : Nat} (h : (List.range' a n).all f = true) :
    ∀ m, a ≤ m → m < a + n → f m = true :=
  fun m h1 h2 => List.all_eq_true.1 h m (List.mem_range'_1.2 ⟨h1, h2⟩)

theorem op_all (o : Fin NO) : opChk o.val = true := by
  have := o.isLt
  have hNO : NO = 367 := rfl
  rcases Nat.lt_or_ge o.val 60 with h | h
  · exact range'_all op_c1 _ (by omega) (by omega)
  rcases Nat.lt_or_ge o.val 120 with h' | h'
  · exact range'_all op_c2 _ (by omega) (by omega)
  rcases Nat.lt_or_ge o.val 180 with h'' | h''
  · exact range'_all op_c3 _ (by omega) (by omega)
  rcases Nat.lt_or_ge o.val 240 with h3 | h3
  · exact range'_all op_c4 _ (by omega) (by omega)
  rcases Nat.lt_or_ge o.val 300 with h4 | h4
  · exact range'_all op_c5 _ (by omega) (by omega)
  · exact range'_all op_c6 _ (by omega) (by omega)

theorem ch_all (c : Fin NC) : chChk c.val = true := by
  have := c.isLt
  have hNC : NC = 465 := rfl
  rcases Nat.lt_or_ge c.val 240 with h | h
  · exact range'_all ch_c1 _ (by omega) (by omega)
  · exact range'_all ch_c2 _ (by omega) (by omega)

theorem chk_of (o : Fin NO) : faChk o = true ∧ jrChk o = true ∧ stChk o = true ∧ srtChk o = true := by
  have := op_all o
  unfold opChk at this
  rw [dif_pos o.isLt] at this
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

theorem ch_sorted (c : Fin NC) : sortedB (cdA c).rq = true ∧ sortedB (cdA c).ak = true := by
  have := ch_all c
  unfold chChk at this
  rw [dif_pos c.isLt] at this
  simp only [Bool.and_eq_true] at this
  exact this



end Formal.Cells.FiniteNetWit2
