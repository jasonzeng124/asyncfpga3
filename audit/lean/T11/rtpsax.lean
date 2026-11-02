import FormalWit.RTPS.All
import FormalWit.RTPS.OAll
open Formal.Target
#check @Formal.Target.DecodedPS.net_wf
#check @Formal.Target.RTPS.Data.roundtrip
#check @Formal.Target.RTPS.Data.o5_gates
example : Formal.Target.DecodedPS.net.gates = Formal.Target.DecodedPS.gates := rfl
#print axioms Formal.Target.DecodedPS.net_wf
#print axioms Formal.Target.RTPS.Data.roundtrip
#print axioms Formal.Target.RTPS.Data.o5_gates
