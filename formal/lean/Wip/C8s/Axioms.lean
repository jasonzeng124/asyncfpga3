import Formal.Net.CapstoneWalk
-- C-8s: #print axioms only; proves nothing.
open Formal.Net.CapNet.Gcd
#print axioms gcd_hw_walk
#print axioms gcd_hw_circuit_safe3
#print axioms gcd_hw_forced3
#print axioms gcd_hw_arbiters_uncontended3
#print axioms walk_ok
#check @gcd_hw_circuit_safe3
