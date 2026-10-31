import Formal.Cells.BWitNet
import Formal.Cells.BWit2Net
import Formal.Cells.BWit3Net
import Formal.Cells.BWit4Net
import Formal.Cells.FiniteNetBoundN

/-! Auditor P17 (B): statements and axioms of the Bwit4 witness, the chunked kernel checks
(cacfac9d) and FiniteNetBoundN (34dfecde). Imports built .oleans only. -/

-- the chunk-combining theorems keep their statements
#check @Formal.Cells.BWit.bop_all
#check @Formal.Cells.BWit2.bop_all
#check @Formal.Cells.BWit3.bopN_all
#check @Formal.Cells.BWit4.bopN_all
#check @Formal.Cells.BWit4.bw_all
#check @Formal.Cells.BWit4.barb_all
#print axioms Formal.Cells.BWit.bop_all
#print axioms Formal.Cells.BWit2.bop_all
#print axioms Formal.Cells.BWit3.bopN_all
#print axioms Formal.Cells.BWit4.bopN_all
#print axioms Formal.Cells.BWit4.bop_k0
#print axioms Formal.Cells.BWit4.bop_k24

-- witnesses
#check @Formal.Cells.BWit4.gcd_hw_fin_netBT_witness
#print axioms Formal.Cells.BWit4.bwit_okT
#print axioms Formal.Cells.BWit4.gcd_hw_fin_netBT_witness
#print axioms Formal.Cells.BWit4.gcd_hw_fin_netBT_consistent
#print axioms Formal.Cells.BWit3.gcd_hw_fin_netBA_witness
#print axioms Formal.Cells.BWit2.gcd_hw_fin_netBM_witness
#print axioms Formal.Cells.BWit.gcd_hw_fin_netB_witness

-- FiniteNetBoundN
#check @Formal.Cells.FiniteNetBoundN.gcd_hw_safe_fin_netBN
#print axioms Formal.Cells.FiniteNetBoundN.bound_censusN
#print axioms Formal.Cells.FiniteNetBoundN.gcd_hw_safe_fin_netBN
#print axioms Formal.Cells.FiniteNetBoundN.FGcdNetOKBN.toOKBT
#print axioms Formal.Cells.FiniteNetBoundT.bound_censusT
#eval Formal.Cells.FiniteNetBoundN.nBothN
#eval Formal.Cells.FiniteNetBoundT.nBothT
