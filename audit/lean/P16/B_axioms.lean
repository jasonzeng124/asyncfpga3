import Formal.Cells.BWit3Net
import Formal.Cells.BWit2Net
import Formal.Cells.BWitNet
import Formal.Cells.FiniteNetBoundT
/-! Auditor P16: axioms of the shard-B results under audit (imports built .oleans only). -/
#print axioms Formal.Cells.FiniteNetBoundA.bound_censusA
#print axioms Formal.Cells.FiniteNetBoundA.gcd_hw_safe_fin_netBA
#print axioms Formal.Cells.FiniteNetBoundT.bound_censusT
#print axioms Formal.Cells.FiniteNetBoundT.gcd_hw_safe_fin_netBT
#print axioms Formal.Cells.BWit3.bwit_okA
#print axioms Formal.Cells.BWit3.gcd_hw_fin_netBA_witness
#print axioms Formal.Cells.BWit3.gcd_hw_fin_netBA_consistent
#print axioms Formal.Cells.FiniteNetComb.fcomb_spec_cell
#check @Formal.Cells.BWit3.gcd_hw_fin_netBA_witness
-- c9ae12c5: both older witnesses with the H_DRV_* fields
#print axioms Formal.Cells.BWit2.gcd_hw_fin_netBM_witness
#print axioms Formal.Cells.BWit.gcd_hw_fin_netB_witness
