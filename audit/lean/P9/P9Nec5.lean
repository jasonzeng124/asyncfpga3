import Formal.Cells.Necessity5Arb
import Formal.Cells.Necessity5Delay
import Formal.Cells.Necessity5Mem
import Formal.Cells.LutFbBridge
/-! P9 audit, item 2. -/
namespace P9Nec5
open Formal.Cells

#check @Necessity5Arb.grant_skew_exact
#check @Necessity5Delay.two_exact
#check @Necessity5Delay.pulse_iff
#check @Necessity5Mem.setup_exact
#check @Necessity5Mem.hold_exact
#check @Necessity5Mem.rdata_exact
#check @Necessity5Mem.clk_high_exact
#check @Necessity5Mem.clk_low_exact
#print axioms Necessity5Arb.grant_skew_exact
#print axioms Necessity5Arb.nonvacuous
#print axioms Necessity5Delay.two_exact
#print axioms Necessity5Delay.flush_not_necessary
#print axioms Necessity5Delay.dack2_glitch
#print axioms Necessity5Mem.setup_exact
#print axioms Necessity5Mem.hold_exact
#print axioms Necessity5Mem.rdata_exact
#print axioms Necessity5Mem.clk_high_exact
#print axioms Necessity5Mem.clk_low_exact

/-- Mutation: grant_skew with one tick of slack is NOT exact (point (L,d5,d6) = (4,1,6)). -/
theorem mut_skew : ¬ (∀ D : ArbBinary.Delays, 0 < D.L →
    (Necessity5Arb.Excl D ↔ (D.d6 ≤ D.d5 + D.L + 1 ∧ D.d5 ≤ D.d6 + D.L + 1))) := by
  intro h
  exact Necessity5Arb.bsx3_points.1 ((h ⟨4, 1, 6⟩ (by decide)).2 ⟨by decide, by decide⟩)

/-- Mutation: three copies, Pulse ↔ Flush is false (so the DACK=2 restriction is load-bearing). -/
theorem mut_three : ¬ (∀ δ w, 1 ≤ w → (Necessity5Delay.Pulse δ 2 w ↔ Necessity5Delay.Flush δ 2 w)) := by
  intro h
  exact Necessity5Delay.flush_not_necessary.1
    ((h _ 1 (by decide)).1 Necessity5Delay.flush_not_necessary.2)

/-- Mutation: the hold bound with +1 slack is not sufficient (port p0 with tHD := 4). -/
def p1 : LibEndMemMlink.MemPort := { Necessity5Mem.p0 with tHD := 4 }
theorem mut_hold : ¬ (∀ m, Necessity5Mem.Same m p1 → m.tClkR + m.tHD ≤ m.tPayNext) := by
  rw [Necessity5Mem.hold_exact p1]; decide

/-! LutFbBridge -/
#check @LutFbBridge.c2_lutFb
#check @LutFbBridge.link_lutFb
#print axioms LutFbBridge.c2_lutFb
#print axioms LutFbBridge.link_lutFb
#print axioms LutFbBridge.fork2_lutFb
#print axioms LutFbBridge.join2_lutFb
#print axioms LutFbBridge.muxn_c2_lutFb
#print axioms LutFbBridge.arb_ack_lutFb
#print axioms LutFbBridge.mux_ack_lutFb
#print axioms LutFbBridge.link_witness
#print axioms LutFbBridge.c2_witness
#print axioms LutFbBridge.no_revert_needed_lutFb
#print axioms LutFbBridge.env_needed_lutFb

end P9Nec5
