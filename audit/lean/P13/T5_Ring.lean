import Formal.Net.RingReset
open Formal.Net Formal.Net.Bridge Formal.Net.RingReset

#check @bdc_closed_ring_empty

-- Hypotheses jointly satisfiable: the constant reset trace is an inertial timed trace of
-- the 3-stage all-bd_c2n ring (lo = hi = 1).
theorem const_timed (n : Nat) :
    Timed (Bridge.RingT.ringNet n 0) (fun _ => 1) (fun _ => 1) (fun _ => Ring.resetState 0) where
  gate i _ := {
    lo_pos := Nat.le_refl _
    cause := fun t h => absurd rfl h
    settle := fun t _ _ => by
      show Ring.resetState 0 i = Ring.gate n 0 false (Ring.resetState 0) i
      rw [Ring.gate_run]; simp [Ring.resetState, Ring.ctl] }
  frame _ _ _ := rfl

example : ∀ t, (fun _ : Nat => Ring.resetState 0) t = Ring.resetState 0 :=
  (bdc_closed_ring_empty 3 (const_timed 3) rfl).2.2

-- The INIT behind `Ring.gate` is the RTL's bd_c2n (cells/rtl/bd_ce.v:49, 64'h00B2_00B2_00B2_00B2).
example : Formal.Cells.CElemFn.INIT_c2n = 0x00B200B200B200B2 := rfl
