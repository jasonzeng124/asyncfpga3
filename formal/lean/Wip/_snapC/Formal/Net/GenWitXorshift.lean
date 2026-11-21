import Formal.Net.GenWitXorshiftData
import Formal.Net.CellBindPersistK

/-!
# Probe C-witgen (xorshift): an ACTIVE joint witness for O4b's generated-cell xorshift capstones

O4b's `xorshift_circuit_safe_gen` (`GenCellK`) and `xorshift_circuit_safe_genP` (`GenCellKP`) had
only the quiet witness (C-wit's run frozen at tick 0). `xch` is a unit-delay run of the
concrete xorshift network at the generated-netlist level (simgen.py; chain shapes as for gcd_hw),
seed = 2463534242, rounds = 4 (the inputs of kernels/xorshift/xorshift.c's main). It meets every hypothesis of both theorems and closes out0 with 2008045182. The value is
`xsSpec 2463534242 4` (decided here) and what gcc computes for xorshift.c's function on these inputs (formal/tools/capwit2/expected.sh), not read from the run.
-/

namespace Formal.Net.CellBind.GenWit.Xorshift
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Wit
open Formal.Net.XorshiftCap Formal.Net.CellBind.GenWit Formal.Net.CellBind.KOps Formal.Net.KCap Formal.Net.KCap.XorshiftInst

set_option maxRecDepth 100000

attribute [local instance] xorKD

def xP (i : Nat) : Bool := kChkGK xcdA (xoxA i) (srcV 2463534242 4) (ops.getD i (K.sink 0))

theorem xcells : (List.range' 0 NO).all xP = true := by decide +kernel

def xch (c : Fin NC) : Chan := wch xcdA c

theorem x_genK : ∀ o : Fin NO, GenCellK xch (srcV 2463534242 4) (KCap.opAt o) := fun o =>
  kChkGK_sound (xoxA o.val) (srcV 2463534242 4) (KCap.opAt o)
    (List.all_eq_true.mp xcells o.val (List.mem_range'_1.2 ⟨Nat.zero_le _, o.isLt⟩))

theorem xcds_len : xcds.length = NC := by decide +kernel
theorem xheld_all : xcds.all heldChk = true := by decide +kernel

theorem x_held : ∀ c : Fin NC, Held (xch c) := by
  intro c
  apply held_of
  apply List.all_eq_true.mp xheld_all
  unfold xcdA
  have h : c.val < xcds.length := by rw [xcds_len]; exact c.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem xstart_rq : (xcdA start).rq = [xStartRise, xStartFall] := by decide +kernel

theorem x_start_once : ∀ t, cnt (riseB (xch start).req) t ≤ 1 := once_of xstart_rq (by decide)

theorem x_out0 : TokAt (xch out0) 0 xOut0Close ∧ (xch out0).dat xOut0Close = 2008045182 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide +kernel

theorem x_expected : XorshiftHw.xsSpec 2463534242 4 = 2008045182 := by decide +kernel

/-- **Active witness, xorshift, O4b (`GenCellK`) and PersistK (`GenCellKP`) jointly.** -/
theorem xorshift_gen_joint_witness :
    ∃ ch : Fin NC → Chan,
      (∀ o : Fin NO, GenCellK ch (srcV 2463534242 4) (KCap.opAt o)) ∧
      (∀ o : Fin NO, PersistK.GenCellKP ch (srcV 2463534242 4) (KCap.opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) ∧
      (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 2008045182) :=
  ⟨xch, x_genK, fun o => PersistK.genP_of xch _ _ (x_genK o), x_held, x_start_once,
    ⟨0, xOut0Close, x_out0⟩⟩

/-- Both capstones applied to the run give 2008045182. -/
theorem xorshift_gen_witness_consistent :
    (∀ k v, TokAt (xch out0) k v → (xch out0).dat v = 2008045182) ∧ TokAt (xch out0) 0 xOut0Close := by
  have h1 := K.xorshift_circuit_safe_gen 2463534242 4 (by decide) xch x_genK x_held x_start_once
  have h2 := PersistK.xorshift_circuit_safe_genP 2463534242 4 (by decide) xch
    (fun o => PersistK.genP_of xch _ _ (x_genK o)) x_held x_start_once
  rw [x_expected] at h1 h2
  exact ⟨h1.1, x_out0.1⟩

end Formal.Net.CellBind.GenWit.Xorshift
