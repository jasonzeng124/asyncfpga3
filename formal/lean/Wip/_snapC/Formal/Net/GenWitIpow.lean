import Formal.Net.GenWitIpowData
import Formal.Net.CellBindPersistK

/-!
# Probe C-witgen (ipow): an ACTIVE joint witness for O4b's generated-cell ipow capstones

O4's H_GEN is unsatisfiable on ipow (`ipow_O4_vacuous`: no `GenCell` for its 3-input compute
unit); O4b's `ipow_circuit_safe_gen` (`GenCellK`) and `ipow_circuit_safe_genP` (`GenCellKP`)
had NO witness at all (no `Cell` run of ipow existed to freeze). `ich` is a unit-delay run of
the concrete 101-channel ipow network at the generated-netlist level (simgen.py; the
bd_join_N3 node of operator 20, chain shapes as for gcd_hw), b = 3, e = 7 (ipow.c's own main).
It meets every hypothesis of both theorems and closes out0 with 2187. The expected value is
`ipowSpec 3 7` (decided here) and agrees with gcc on kernels/ipow/ipow.c
(formal/tools/capwit3/expected.sh), not read from the run.
-/

namespace Formal.Net.CellBind.GenWit.Ipow
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Wit
open Formal.Net.IpowCap Formal.Net.CellBind.GenWit Formal.Net.CellBind.KOps

set_option maxRecDepth 100000

def iP (i : Nat) : Bool := kChkGK icdA (ioxA i) (srcV 3 7) (ops.getD i (K.sink 0))

theorem icells : (List.range' 0 83).all iP = true := by decide +kernel

def ich (c : Fin NC) : Chan := wch icdA c

theorem i_genK : ∀ o : Fin NO, GenCellK ich (srcV 3 7) (opAt o) := fun o =>
  kChkGK_sound (ioxA o.val) (srcV 3 7) (opAt o)
    (List.all_eq_true.mp icells o.val (List.mem_range'_1.2 ⟨Nat.zero_le _, o.isLt⟩))

theorem icds_len : icds.length = NC := by decide +kernel
theorem iheld_all : icds.all heldChk = true := by decide +kernel

theorem i_held : ∀ c : Fin NC, Held (ich c) := by
  intro c
  apply held_of
  apply List.all_eq_true.mp iheld_all
  unfold icdA
  have h : c.val < icds.length := by rw [icds_len]; exact c.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem istart_rq : (icdA start).rq = [iStartRise, iStartFall] := by decide +kernel

theorem i_start_once : ∀ t, cnt (riseB (ich start).req) t ≤ 1 := once_of istart_rq (by decide)

theorem i_out0 : TokAt (ich out0) 0 iOut0Close ∧ (ich out0).dat iOut0Close = 2187 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide +kernel

theorem ipow_expected : IpowHw.ipowSpec 3 7 = 2187 := by decide +kernel

/-- **Active witness, ipow, O4b (`GenCellK`) and PersistK (`GenCellKP`) jointly.** -/
theorem ipow_gen_joint_witness :
    ∃ ch : Fin NC → Chan,
      (∀ o : Fin NO, GenCellK ch (srcV 3 7) (opAt o)) ∧
      (∀ o : Fin NO, PersistK.GenCellKP ch (srcV 3 7) (opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) ∧
      (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 2187) :=
  ⟨ich, i_genK, fun o => PersistK.genP_of ich _ _ (i_genK o), i_held, i_start_once, ⟨0, iOut0Close, i_out0⟩⟩

/-- Both ipow capstones applied to the run give 2187 = `ipowSpec 3 7`. -/
theorem ipow_gen_witness_consistent :
    (∀ k v, TokAt (ich out0) k v → (ich out0).dat v = 2187) ∧ TokAt (ich out0) 0 iOut0Close := by
  have h1 := K.ipow_circuit_safe_gen 3 7 (by decide) ich i_genK i_held i_start_once
  have h2 := PersistK.ipow_circuit_safe_genP 3 7 (by decide) ich
    (fun o => PersistK.genP_of ich _ _ (i_genK o)) i_held i_start_once
  rw [ipow_expected] at h1 h2
  exact ⟨h1.1, i_out0.1⟩

end Formal.Net.CellBind.GenWit.Ipow
