import Formal.Net.CapstoneWitness
import Formal.Net.CapstoneWitness3
/-! C-8t: `#print axioms` and `#check` only; proves nothing. -/
open Formal.Net.CapNet.Wit Formal.Net.CapNet.Gcd
#check @gcd_hw_joint_witness
#check @gcd_hw_witness_consistent
#check @gcd_hw_circuit_safe''
#print axioms gcd_hw_joint_witness
#print axioms gcd_hw_witness_consistent
#print axioms kChk_sound
#print axioms walkOK_of
#print axioms yW_good
#print axioms gcd_hw_joint_witness3
#print axioms gcd_hw_witness3_consistent
