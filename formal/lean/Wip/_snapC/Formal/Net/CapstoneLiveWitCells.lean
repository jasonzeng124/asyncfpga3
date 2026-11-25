import Formal.Net.CapstoneLiveWitData

/-!
# Probe C-8z2 (2): the liveness witness run meets H_CELLS, H_BUNDLE, H_START_ONCE, H_START_ENV

Kernel checks (`decide +kernel`, in chunks) of 8t's event-list checkers on the run `chL`
(`CapstoneLiveWitData`, a = 12, b = 18, free-running a/b sources):
* `l_cells`: every one of the 367 operators meets its gate model with the internal traces
  `itrW cdW` explicit (`CellI`, the form `gcd_hw_live_final` asks for);
* `l_held`: every channel is bundled (`Held`);
* `l_start_once`, `l_start_env`: `start` rises once, at tick 0 (H_START_ONCE, H_START_ENV 1);
* `l_out0`: out0's first token closes at `closeL`, carrying 6.
-/

namespace Formal.Net.CapNet.LiveWit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Live Formal.Net.CapNet.Wit

set_option maxRecDepth 100000

theorem lcells1 : (ops.take 90).all (fun k => kChk cdW (srcV Aw Bw) k) = true := by decide +kernel
theorem lcells2 : ((ops.drop 90).take 90).all (fun k => kChk cdW (srcV Aw Bw) k) = true := by decide +kernel
theorem lcells3 : (((ops.drop 90).drop 90).take 90).all (fun k => kChk cdW (srcV Aw Bw) k) = true := by
  decide +kernel
theorem lcells4 : (((ops.drop 90).drop 90).drop 90).all (fun k => kChk cdW (srcV Aw Bw) k) = true := by
  decide +kernel

theorem lcells_all : ops.all (fun k => kChk cdW (srcV Aw Bw) k) = true := by
  rw [← List.take_append_drop 90 ops, List.all_append, lcells1, ← List.take_append_drop 90 (ops.drop 90),
    List.all_append, lcells2, ← List.take_append_drop 90 ((ops.drop 90).drop 90), List.all_append, lcells3,
    lcells4]; rfl

/-- H_CELLS (internal traces explicit) holds for the run. -/
theorem l_cells : ∀ p : Fin NO, CellI chL (srcV Aw Bw) (itrW cdW) p (opAt p) := fun p =>
  cellI_of (srcV Aw Bw) p (List.all_eq_true.mp lcells_all _ getD_mem)

theorem cdsL_len : cdsL.length = NC := by decide +kernel

theorem lheld_all : cdsL.all heldChk = true := by decide +kernel

/-- H_BUNDLE holds for the run. -/
theorem l_held : ∀ c : Fin NC, Held (chL c) := by
  intro c
  apply held_of
  apply List.all_eq_true.mp lheld_all
  unfold cdW
  have h : c.val < cdsL.length := by rw [cdsL_len]; exact c.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem lstart_rq : (cdW start).rq = [0, 99] := by decide +kernel

/-- H_START_ONCE holds for the run. -/
theorem l_start_once : ∀ t, cnt (riseB (chL start).req) t ≤ 1 :=
  once_of lstart_rq (by decide)

/-- H_START_ENV 1 holds for the run. -/
theorem l_start_env : Live.Nd.StartEnv 1 (chL start) :=
  start_env (L := [99]) lstart_rq (by decide)

/-- out0's first token closes at `closeL`, and carries 6. -/
theorem l_out0 : TokAt (chL out0) 0 closeL ∧ (chL out0).dat closeL = 6 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide +kernel

end Formal.Net.CapNet.LiveWit
