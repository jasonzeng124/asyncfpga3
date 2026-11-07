import Formal.Net.CollatzWitData
import Formal.Net.KernelCapCollatz

/-!
# Probe C-wit: `collatz_circuit_safe` (C-8y2) is not vacuous

One explicit run `chC` of the concrete 81-channel collatz network (`CollatzWitData`, generated
by `formal/tools/capwit2/gen_wit.py collatz`: every gate of every cell model with delay 1, each
source offers once, sinks acknowledge after one tick) on n = 7 meets H_CELLS, H_BUNDLE and
H_START_ONCE (at `srcC 7 200`: fuel 200, which the circuit ignores) and latches 16 on out0.

The expected value 16 (the stopping time of 7) is what the C function in
`kernels/collatz/collatz.c` returns (`formal/tools/capwit2/expected.sh`); it is not read from the
run. `c_expected` checks `collatzC 200 7 = some 16` (the termination hypothesis of
`collatz_circuit_safe`), and `collatz_witness_consistent` applies the theorem to the run.

Checks: `decide +kernel` over the event lists with C-8t's checker (`CapstoneWitnessLib`);
no `native_decide`.
-/

namespace Formal.Net.KCap.CollatzWit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Wit
open Formal.Net.KCap Formal.Net.KCap.CollatzInst

set_option maxRecDepth 100000

attribute [local instance] collatzKD

/-- The run. -/
def chC : Fin CollatzCap.NC → Chan := wch cdA

theorem ccells : CollatzCap.ops.all (fun k => kChk cdA (srcC 7 200) k) = true := by
  decide +kernel

theorem ops_len : CollatzCap.ops.length = CollatzCap.NO := by decide +kernel

theorem getD_mem' {o : Fin CollatzCap.NO} : KCap.opAt o ∈ CollatzCap.ops := by
  show CollatzCap.ops.getD o.val (K.sink 0) ∈ CollatzCap.ops
  have h : o.val < CollatzCap.ops.length := by rw [ops_len]; exact o.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem c_cells : ∀ o : Fin CollatzCap.NO, Cell chC (srcC 7 200) (KCap.opAt o) :=
  fun o => kChk_sound (srcC 7 200) (KCap.opAt o) (List.all_eq_true.mp ccells _ getD_mem')

theorem cds_len : cds.length = CollatzCap.NC := by decide +kernel
theorem held_all : cds.all heldChk = true := by decide +kernel

theorem c_held : ∀ c : Fin CollatzCap.NC, Held (chC c) := by
  intro c
  apply held_of
  apply List.all_eq_true.mp held_all
  unfold cdA
  have h : c.val < cds.length := by rw [cds_len]; exact c.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem start_rq : (cdA CollatzCap.start).rq = [0, 39] := by decide +kernel

theorem c_start_once : ∀ t, cnt (riseB (chC CollatzCap.start).req) t ≤ 1 :=
  once_of start_rq (by decide)

theorem c_out0 : TokAt (chC CollatzCap.out0) 0 979 ∧ (chC CollatzCap.out0).dat 979 = 16 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide +kernel

/-- The C result for the witness input agrees with the Lean transcription (fuel 200). -/
theorem c_expected : CollatzHw.collatzC 200 7 = some 16 := by decide +kernel

/-- **A non-quiet joint witness for `collatz_circuit_safe`.** -/
theorem collatz_joint_witness :
    ∃ ch : Fin CollatzCap.NC → Chan,
      (∀ o : Fin CollatzCap.NO, Cell ch (srcC 7 200) (KCap.opAt o)) ∧   -- H_CELLS
      (∀ c, Held (ch c)) ∧                                                            -- H_BUNDLE
      (∀ t, Handshake.cnt (riseB (ch CollatzCap.start).req) t ≤ 1) ∧                 -- H_START_ONCE
      (∃ k e, TokAt (ch CollatzCap.out0) k e ∧ (ch CollatzCap.out0).dat e = 16) :=
  ⟨chC, c_cells, c_held, c_start_once, 0, 979, c_out0⟩

theorem collatz_witness_consistent :
    (∀ k e, TokAt (chC CollatzCap.out0) k e → (chC CollatzCap.out0).dat e = 16) ∧
    TokAt (chC CollatzCap.out0) 0 979 := by
  exact ⟨(collatz_circuit_safe 7 200 16 c_expected chC c_cells c_held c_start_once).1, c_out0.1⟩

end Formal.Net.KCap.CollatzWit
