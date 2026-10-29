import Formal.Net.RingResetCert
import Formal.Net.RingTimedPure
/-! P10c item 6: C-9d rings (f0abe30). -/
#print axioms Formal.Net.RingReset.bdc_closed_ring_empty
#print axioms Formal.Net.RingReset.mux_j0_rst_clear
#print axioms Formal.Net.RingReset.c2n_rst_clear
#print axioms Formal.Net.RingResetCert.loop3_good
#print axioms Formal.Net.RingResetCert.loop4_good
#print axioms Formal.Net.RingResetCert.loop5_good
#print axioms Formal.Net.RingResetCert.loop1_stuck
#print axioms Formal.Net.RingResetCert.loop2_stuck
#print axioms Formal.Net.RingResetCert.loop3_exits
#print axioms Formal.Net.RingTimed.timed_ring_three
#print axioms Formal.Net.RingTimed.timed_ring_never
#print axioms Formal.Net.RingTimed.ring_no_runt
#print axioms Formal.Net.RingTimedPure.ring_pure_safe_live
#print axioms Formal.Net.RingTimedPure.ring_pure_dead
#print axioms Formal.Net.RingTimedPure.pure_noOvertake

namespace P10c6
open Formal.Net Formal.Net.RingReset
/-- My INIT cross-check: the Lean constants equal the RTL text (cells/rtl/bd_mux.v, bd_ctl.v). -/
example : INIT_mux_j0 = 0x0000AE080000AE08 ∧ INIT_mux_j1 = 0x0000EA800000EA80 ∧
    INIT_steer = 0x8888888822222222 ∧ INIT_or2 = 0xE ∧ INIT_src = 0x1 := ⟨rfl, rfl, rfl, rfl, rfl⟩
/-- Mutation (INIT): set one bit of uj0's rst=1 half and the reset-clear fails. -/
example : ¬ ∀ a b c q : Bool, lutB (INIT_mux_j0 ||| (1 <<< 16)) [a, b, c, q, true, false] = false := by
  decide
/-- Mutation (certificate): the N = 2 stuck state is NOT good (the stop clause fails), so goodB
is a real filter, not a tautology. -/
example : goodB 2 (lastOf (s0 2) RingResetCert.P2) = false := by decide +kernel
example : goodB 1 (lastOf (s0 1) RingResetCert.P1) = false := by decide +kernel
/-- The iff's left side at N = 2 is false (unit-delay trace, frozen). -/
example : ¬ (∀ (lo hi : Nat → Nat) (x : Nat → Ring.State), Bridge.Timed (Bridge.RingT.ringNet 2 1) lo hi x →
    x 0 = Ring.resetState 1 → RingTimed.LiveAfter 2 hi x) := by
  intro h
  have := (RingTimed.timed_ring_three 2 1 (by decide) (by decide)).1 h
  omega
end P10c6
