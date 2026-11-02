import FormalWit.RT.All
import FormalWit.RT.OAll
open Formal.Target
#check @Formal.Target.RT.Data.roundtrip
#check @Formal.Target.RT.Data.o5_gates
-- the round trip's gate list is the refutation's netlist
example : Formal.Target.Decoded.net.gates = Formal.Target.Decoded.gates := rfl
#print axioms Formal.Target.RT.Data.roundtrip
#print axioms Formal.Target.RT.Data.o5_gates
