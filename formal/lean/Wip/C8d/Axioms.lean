import Formal.Net.BridgeWire
import Formal.Net.BridgeRing
import Formal.Net.BridgeTransport
/-! Axiom audit for probe 8d (run: ../slot.sh lean Wip/C8d/Axioms.lean). -/
open Formal.Net.Bridge
#print axioms goodF
#print axioms timed_runF
#print axioms fires_withinF
#print axioms realize
#print axioms unit_timed
#print axioms inertial_bounded
#print axioms Inertial.noOvertake
#print axioms Transport.transport_breaks_si
#print axioms Transport.cx_inertial_safe
#print axioms RingT.timed_ring_safe
#print axioms RingT.timed_ring_live
#print axioms RingT.timed_ring_every_stage
#print axioms RingT.timed_ring_k_tokens
#print axioms RingT.timed_ring_dead
#print axioms RingT.timed_ring_degenerate
#print axioms Wire.timed_fork3
#print axioms Wire.timed_fork4
#print axioms Wire.fb3_not_persistent
#print axioms Wire.fb3_timed_token_lost
