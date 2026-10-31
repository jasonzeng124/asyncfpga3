import Formal.Net.CapstoneWitnessData
import Formal.Net.CapstoneCutSpine

/-!
# Probe C-8t: the generated gcd_hw run meets H_CELLS, H_BUNDLE and H_START_ONCE, and closes out0

Kernel checks (`decide +kernel`, in chunks) of the event-list checkers of
`CapstoneWitnessLib` on the run `chW` of `CapstoneWitnessData` (a = 12, b = 18):
* `w_cells`: every one of the 367 operators meets its gate model (`Cell chW (srcV 12 18)`);
* `w_held`: every one of the 465 channels is bundled (`Held`);
* `w_start_once`: the start channel's request rises at most once;
* `w_out0`: out0's acknowledge falls (its first token closes) at `out0Close`, carrying 6.
-/

namespace Formal.Net.CapNet.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd

set_option maxRecDepth 100000

theorem cells1 : (ops.take 90).all (fun k => kChk cdA (srcV A0 B0) k) = true := by decide +kernel
theorem cells2 : ((ops.drop 90).take 90).all (fun k => kChk cdA (srcV A0 B0) k) = true := by decide +kernel
theorem cells3 : (((ops.drop 90).drop 90).take 90).all (fun k => kChk cdA (srcV A0 B0) k) = true := by
  decide +kernel
theorem cells4 : (((ops.drop 90).drop 90).drop 90).all (fun k => kChk cdA (srcV A0 B0) k) = true := by
  decide +kernel

theorem cells_all : ops.all (fun k => kChk cdA (srcV A0 B0) k) = true := by
  rw [← List.take_append_drop 90 ops, List.all_append, cells1, ← List.take_append_drop 90 (ops.drop 90),
    List.all_append, cells2, ← List.take_append_drop 90 ((ops.drop 90).drop 90), List.all_append, cells3,
    cells4]; rfl

/-- H_CELLS holds for the run. -/
theorem w_cells : ∀ o : Fin NO, Cell chW (srcV A0 B0) (opAt o) := fun o =>
  kChk_sound (srcV A0 B0) (opAt o) (List.all_eq_true.mp cells_all _ getD_mem)

theorem cds_len : cds.length = NC := by decide +kernel

theorem held_all : cds.all heldChk = true := by decide +kernel

/-- H_BUNDLE holds for the run. -/
theorem w_held : ∀ c : Fin NC, Held (chW c) := by
  intro c
  apply held_of
  apply List.all_eq_true.mp held_all
  unfold cdA
  have h : c.val < cds.length := by rw [cds_len]; exact c.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem start_rq : (cdA start).rq = [startRise, startFall] := by decide +kernel

/-- H_START_ONCE holds for the run. -/
theorem w_start_once : ∀ t, cnt (riseB (chW start).req) t ≤ 1 :=
  once_of start_rq (by decide)

/-- out0's first token closes at `out0Close`, and carries 6. -/
theorem w_out0 : TokAt (chW out0) 0 out0Close ∧ (chW out0).dat out0Close = 6 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide +kernel

end Formal.Net.CapNet.Wit
