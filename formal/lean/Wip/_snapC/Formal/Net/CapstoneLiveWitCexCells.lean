import Formal.Net.CapstoneLiveWitCexData

/-!
# Probe C-8z2 (7): the counterexample run meets H_CELLS, H_BUNDLE, H_START_ONCE, H_START_ENV

Kernel checks on `chX` (`CapstoneLiveWitCexData`: a = 12, b = 18, `start` never released).
-/

namespace Formal.Net.CapNet.LiveWit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Live Formal.Net.CapNet.Wit

set_option maxRecDepth 100000

theorem xcells1 : (ops.take 180).all (fun k => kChk cdX (srcV 12 18) k) = true := by decide +kernel
theorem xcells2 : (ops.drop 180).all (fun k => kChk cdX (srcV 12 18) k) = true := by decide +kernel

theorem xcells_all : ops.all (fun k => kChk cdX (srcV 12 18) k) = true := by
  rw [← List.take_append_drop 180 ops, List.all_append, xcells1, xcells2]; rfl

theorem x_cells : ∀ p : Fin NO, CellI chX (srcV 12 18) (itrW cdX) p (opAt p) := fun p =>
  cellI_of (srcV 12 18) p (List.all_eq_true.mp xcells_all _ getD_mem)

theorem cdsX_len : cdsX.length = NC := by decide +kernel

theorem xheld_all : cdsX.all heldChk = true := by decide +kernel

theorem x_held : ∀ c : Fin NC, Held (chX c) := by
  intro c
  apply held_of
  apply List.all_eq_true.mp xheld_all
  unfold cdX
  have h : c.val < cdsX.length := by rw [cdsX_len]; exact c.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem xstart_rq : (cdX start).rq = [0] := by decide +kernel
theorem xstart_ak : (cdX start).ak = [98] := by decide +kernel
theorem xout0_ak : (cdX out0).ak = [] := by decide +kernel

theorem x_start_once : ∀ t, cnt (riseB (chX start).req) t ≤ 1 := once_of1 xstart_rq

theorem x_start_env : Live.Nd.StartEnv 1 (chX start) :=
  start_env (L := []) xstart_rq (by decide)

/-- out0's acknowledge never falls: no out0 token ever closes. -/
theorem x_never : ∀ t, cnt (fallB (chX out0).ack) t = 0 := never_close xout0_ak

end Formal.Net.CapNet.LiveWit
