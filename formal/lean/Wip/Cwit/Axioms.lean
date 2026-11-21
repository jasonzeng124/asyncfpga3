import Formal.Net.RigAllWit
import Formal.Net.XorshiftWit
import Formal.Net.CollatzWit

/-! C-wit: the witness statements and their axioms (`#check` / `#print axioms` only). -/

#check @Formal.Net.CapNet.RigWit.gcd_rig_all_witness
#print axioms Formal.Net.CapNet.RigWit.gcd_rig_all_witness
#print axioms Formal.Net.CapNet.RigWit.gcd_rig_all_witness_consistent
#check @Formal.Net.CapNet.Gcd.gcd_rig_all
#check @Formal.Net.KCap.XorshiftWit.xorshift_joint_witness
#print axioms Formal.Net.KCap.XorshiftWit.xorshift_joint_witness
#print axioms Formal.Net.KCap.XorshiftWit.xorshift_witness_consistent
#check @Formal.Net.KCap.CollatzWit.collatz_joint_witness
#print axioms Formal.Net.KCap.CollatzWit.collatz_joint_witness
#print axioms Formal.Net.KCap.CollatzWit.collatz_witness_consistent
