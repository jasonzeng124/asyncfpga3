import Formal.Net.GenWitCollatzData
import Formal.Net.CellBindPersistK

/-!
# Probe C-witgen (collatz): an ACTIVE joint witness for O4b's generated-cell collatz capstones

O4b's `collatz_circuit_safe_gen` (`GenCellK`) and `collatz_circuit_safe_genP` (`GenCellKP`) had
only the quiet witness (C-wit's run frozen at tick 0). `cch` is a unit-delay run of the
concrete collatz network at the generated-netlist level (simgen.py; chain shapes as for gcd_hw; its 3-input compute unit is the bd_join_N3 node),
n = 7, fuel 200 (the circuit ignores the fuel; C-wit's input). It meets every hypothesis of both theorems and closes out0 with 16. The value is
`collatzC 200 7 = some 16` (decided here; the termination hypothesis of the capstones) and what gcc computes for collatz.c's function (formal/tools/capwit2/expected.sh), not read from the run.
-/

namespace Formal.Net.CellBind.GenWit.Collatz
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Wit
open Formal.Net.CollatzCap Formal.Net.CellBind.GenWit Formal.Net.CellBind.KOps Formal.Net.KCap Formal.Net.KCap.CollatzInst

set_option maxRecDepth 100000

attribute [local instance] collatzKD

def cP (i : Nat) : Bool := kChkGK ccdA (coxA i) (srcC 7 200) (ops.getD i (K.sink 0))

theorem ccells0 : (List.range' 0 6).all cP = true := by decide +kernel
theorem ccells1 : (List.range' 6 6).all cP = true := by decide +kernel
theorem ccells2 : (List.range' 12 6).all cP = true := by decide +kernel
theorem ccells3 : (List.range' 18 6).all cP = true := by decide +kernel
theorem ccells4 : (List.range' 24 6).all cP = true := by decide +kernel
theorem ccells5 : (List.range' 30 6).all cP = true := by decide +kernel
theorem ccells6 : (List.range' 36 6).all cP = true := by decide +kernel
theorem ccells7 : (List.range' 42 6).all cP = true := by decide +kernel
theorem ccells8 : (List.range' 48 6).all cP = true := by decide +kernel
theorem ccells9 : (List.range' 54 6).all cP = true := by decide +kernel
theorem ccells10 : (List.range' 60 6).all cP = true := by decide +kernel

/-- Collatz's long loop makes every signal toggle ~34 times; the per-operator check is quadratic
in that, so the kernel check is split into chunks of 6 operators (peak memory). -/
theorem ccells : (List.range' 0 NO).all cP = true := by
  have e : List.range' 0 NO = List.range' 0 6 ++ List.range' 6 6 ++ List.range' 12 6 ++ List.range' 18 6 ++ List.range' 24 6 ++ List.range' 30 6 ++ List.range' 36 6 ++ List.range' 42 6 ++ List.range' 48 6 ++ List.range' 54 6 ++ List.range' 60 6 := by decide
  rw [e]; simp only [List.all_append, ccells0, ccells1, ccells2, ccells3, ccells4, ccells5, ccells6, ccells7, ccells8, ccells9, ccells10, Bool.and_self]

def cch (c : Fin NC) : Chan := wch ccdA c

theorem c_genK : ∀ o : Fin NO, GenCellK cch (srcC 7 200) (KCap.opAt o) := fun o =>
  kChkGK_sound (coxA o.val) (srcC 7 200) (KCap.opAt o)
    (List.all_eq_true.mp ccells o.val (List.mem_range'_1.2 ⟨Nat.zero_le _, o.isLt⟩))

theorem ccds_len : ccds.length = NC := by decide +kernel
theorem cheld_all : ccds.all heldChk = true := by decide +kernel

theorem c_held : ∀ c : Fin NC, Held (cch c) := by
  intro c
  apply held_of
  apply List.all_eq_true.mp cheld_all
  unfold ccdA
  have h : c.val < ccds.length := by rw [ccds_len]; exact c.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem cstart_rq : (ccdA start).rq = [cStartRise, cStartFall] := by decide +kernel

theorem c_start_once : ∀ t, cnt (riseB (cch start).req) t ≤ 1 := once_of cstart_rq (by decide)

theorem c_out0 : TokAt (cch out0) 0 cOut0Close ∧ (cch out0).dat cOut0Close = 16 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide +kernel

theorem c_expected : CollatzHw.collatzC 200 7 = some 16 := by decide +kernel

/-- **Active witness, collatz, O4b (`GenCellK`) and PersistK (`GenCellKP`) jointly.** -/
theorem collatz_gen_joint_witness :
    ∃ ch : Fin NC → Chan,
      (∀ o : Fin NO, GenCellK ch (srcC 7 200) (KCap.opAt o)) ∧
      (∀ o : Fin NO, PersistK.GenCellKP ch (srcC 7 200) (KCap.opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) ∧
      (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 16) :=
  ⟨cch, c_genK, fun o => PersistK.genP_of cch _ _ (c_genK o), c_held, c_start_once,
    ⟨0, cOut0Close, c_out0⟩⟩

/-- Both capstones applied to the run give 16. -/
theorem collatz_gen_witness_consistent :
    (∀ k v, TokAt (cch out0) k v → (cch out0).dat v = 16) ∧ TokAt (cch out0) 0 cOut0Close := by
  have h1 := K.collatz_circuit_safe_gen 7 200 16 c_expected cch c_genK c_held c_start_once
  have h2 := PersistK.collatz_circuit_safe_genP 7 200 16 c_expected cch
    (fun o => PersistK.genP_of cch _ _ (c_genK o)) c_held c_start_once
  skip
  exact ⟨h1.1, c_out0.1⟩

end Formal.Net.CellBind.GenWit.Collatz
