import Formal.Cells.BWitNet
/-! Auditor P15bc: the 63/175 witness after 076af340 (selects bound to bit 0), not built by the
auditor's lake build of f40e003a (BWitNChk OOM-killed, rc 137). Checked here against oleans of
BWitNChk/BWitNet compiled by the auditor into the scratchpad. -/
#check @Formal.Cells.BWit.gcd_hw_fin_netB_witness
#print axioms Formal.Cells.BWit.gcd_hw_fin_netB_witness
#print axioms Formal.Cells.BWit.bwit_ok
