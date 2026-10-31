import Formal.Net.EndToEndToy
/-! Axiom audit for probe C-8e (proves nothing). -/
open Formal.Net.EndToEnd Formal.Net.EndToEnd.Toy
#print axioms race2_sound
#print axioms timing_of_check
#print axioms Formal.Net.EndToEnd.PinLink.protocol
#print axioms latch_contract
#print axioms end_to_end
#print axioms good_check
#print axioms good_fifo
#print axioms bad_rejects
#print axioms bad_counterexample
#print axioms good_delivers
