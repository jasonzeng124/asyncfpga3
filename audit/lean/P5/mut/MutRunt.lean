import Formal.Timing.RuntAckInst
open Formal.Timing.RuntAck Formal.Timing.RuntAck.Inst
-- M: server path P := 0 on a live-runt row (gcd_hw_2 merge10.uarb1 client 2, FMIN) -> verdict flips
#eval (g2_merge10_uarb1_FMIN_c2.W, g2_merge10_uarb1_FMIN_c2.margin)
theorem mut_P0 : okAck { g2_merge10_uarb1_FMIN_c2 with P := 0 } = false := by decide
#print axioms inst_no_extra_ack2
#print axioms inst_idx_clean2
#print axioms g2_merge10_uarb1_FMIN_c2_ack
