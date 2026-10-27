import Formal.Net.Import.Proofs
open Formal.Net.Import Formal.Net.Import.Gen Formal.Cells
#print axioms Formal.Net.Import.Proofs.bd_c2_next_spec
#print axioms Formal.Net.Import.Proofs.bd_arbiter_next_K
#print axioms Formal.Net.Import.Proofs.bd_arbiter_next_spec
#print axioms Formal.Net.Import.Proofs.bd_latch_W3_next_spec
#print axioms Formal.Net.Import.Proofs.arbiter_kleene_exclusion
-- audit: concrete evaluation sanity (state actually changes)
#eval bd_c2.next boolSem [true, true, false] [false]
#eval bd_c2.next boolSem [true, true, true] [true]
-- audit: B's Kleene "spec" for C2 is literally lutK of B's INIT constant
example : Formal.Cells.CElemFn.INIT_c2 = 0x00E800E800E800E8 := rfl
