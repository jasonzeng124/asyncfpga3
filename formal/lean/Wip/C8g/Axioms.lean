import Formal.Net.MullerTimedInst
import Formal.Net.MullerTimedCx
open Formal.Net.Muller Formal.Net.MullerTimed
#print axioms timed_good
#print axioms fb_settled
#print axioms timed3_reach
#print axioms timed3_protocol
#print axioms timed3_token_order
#print axioms timed3_hazard_free
#print axioms sim_timed
#print axioms cx_timed
#print axioms cx_violates
#print axioms cx_protocol_broken
#print axioms cx_glitch
#print axioms boundary_function_hazard
-- uncertified evaluations (compiled code): n = 4 certificate passes
#eval checkT 4
