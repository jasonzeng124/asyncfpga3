import Formal.Net.RigAllWitData
import Formal.Net.CapstoneCutSpine

/-!
# Probe C-wit: the generated gcd_rig run meets CellR, H_BUNDLE and RigEnv

Kernel checks (`decide +kernel`, in chunks; no `native_decide`) of the checkers of
`RigAllWitLib` on the run `chR` of `RigAllWitData` (gcd_hw on a = 12, b = 18 inside gcd_rig's
environment, three start offers):
* `r_cells`: every one of the 367 operators meets its gate model, with `Src.iz` dropped
  (`CellR chR (srcV 12 18)`); the three source requests start HIGH (gcd_rig's reset level);
* `r_held`: every one of the 465 channels is bundled (`Held`);
* `r_env`: `RigEnv (chR start).req (chR out0).ack` (the rig's uenv1/uenv0 gate facts);
* the events: start is high at tick 0 and re-offered at 432 and 865; out0 offers at 430, 863,
  1296 and closes (acknowledge falls) at 474 and 907, carrying 6 each time.
-/

namespace Formal.Net.CapNet.RigWit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd

set_option maxRecDepth 100000

/-- The run. -/
def chR : Fin NC → Chan := wch cdA

theorem rcells1 : (ops.take 92).all (fun k => kChkR cdA (srcV 12 18) k) = true := by decide +kernel
theorem rcells2 : ((ops.drop 92).take 92).all (fun k => kChkR cdA (srcV 12 18) k) = true := by
  decide +kernel
theorem rcells3 : (((ops.drop 92).drop 92).take 92).all (fun k => kChkR cdA (srcV 12 18) k) = true := by
  decide +kernel
theorem rcells4 : (((ops.drop 92).drop 92).drop 92).all (fun k => kChkR cdA (srcV 12 18) k) = true := by
  decide +kernel

theorem rcells_all : ops.all (fun k => kChkR cdA (srcV 12 18) k) = true := by
  rw [← List.take_append_drop 92 ops, List.all_append, rcells1, ← List.take_append_drop 92 (ops.drop 92),
    List.all_append, rcells2, ← List.take_append_drop 92 ((ops.drop 92).drop 92), List.all_append, rcells3,
    rcells4]; rfl

/-- H_CELLS without `Src.iz` (`CellR`) holds for the run. -/
theorem r_cells : ∀ o : Fin NO, CellR chR (srcV 12 18) (opAt o) := fun o =>
  kChkR_sound (srcV 12 18) (opAt o) (List.all_eq_true.mp rcells_all _ getD_mem)

theorem cds_len : cds.length = NC := by decide +kernel

theorem held_all : cds.all heldChk = true := by decide +kernel

/-- H_BUNDLE holds for the run. -/
theorem r_held : ∀ c : Fin NC, Held (chR c) := by
  intro c
  apply held_of
  apply List.all_eq_true.mp held_all
  unfold cdA
  have h : c.val < cds.length := by rw [cds_len]; exact c.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem env_all : envChk (cdA start) (cdA out0).ak = true := by decide +kernel

/-- The rig's environment gates hold for the run. -/
theorem r_env : RigEnv (chR start).req (chR out0).ack := env_of env_all

/-- start's request is high at reset release (gcd_rig's `bd_c2n_set`) and is re-offered twice:
at 432, while out0's first handshake is still open (it closes at 474), and at 865. -/
theorem r_start : (chR start).req 0 = true ∧ OffAt (chR start) 0 432 ∧ OffAt (chR start) 1 865 ∧
    (cdA start).rq = [99, 432, 532, 865, 965] := by
  refine ⟨by decide +kernel, ⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩,
    by decide +kernel⟩

/-- out0 offers three tokens (request rises at 430, 863, 1296) and two of them close
(acknowledge falls at 474, 907); the bus is 6 at each. -/
theorem r_out0 :
    (OffAt (chR out0) 0 430 ∧ (chR out0).dat 431 = 6) ∧
    (OffAt (chR out0) 1 863 ∧ (chR out0).dat 864 = 6) ∧
    (OffAt (chR out0) 2 1296 ∧ (chR out0).dat 1297 = 6) ∧
    (TokAt (chR out0) 0 474 ∧ (chR out0).dat 474 = 6) ∧
    (TokAt (chR out0) 1 907 ∧ (chR out0).dat 907 = 6) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩ <;> decide +kernel

end Formal.Net.CapNet.RigWit
