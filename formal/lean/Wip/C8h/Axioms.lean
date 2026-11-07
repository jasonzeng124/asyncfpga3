import Formal.Net.PerLink
import Formal.Net.PerLinkPin
import Formal.Net.PerLinkEvent
import Formal.Net.EndToEnd2
import Formal.Net.EndToEnd2Toy
-- proves nothing: prints the axioms of the main theorems of probe C-8h
open Formal.Net.Handshake Formal.Net.PerLink Formal.Net.PerLink.Toy
#print axioms muller_pipeline2
#print axioms muller_pipeline_of_2
#print axioms ELink.inv
#print axioms latch_bit2
#print axioms end_to_end2
#print axioms end_to_end_fixed
#print axioms event_epin
#print axioms or2_epin
#print axioms bd_echo
#print axioms split_global_rejects
#print axioms split_check2
#print axioms split_fifo
#print axioms dack_check2
#print axioms dack_band_rejects
#print axioms bad_check2
