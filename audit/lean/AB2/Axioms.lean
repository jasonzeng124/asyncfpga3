import Formal.Core.XSim
import Formal.Core.Delay.SAF
import Formal.Core.LutAudit
import Formal.Cells.ArbHeldTimed2
import Formal.Cells.LibCtlMergeMux
import Formal.Cells.LibEndMemMlink
import Formal.Cells.ArbBinary
import Formal.Cells.TernaryPhases
import Formal.Cells.MuxTree
open Formal.Core Formal.Cells
#print axioms XSim.sound
#print axioms XSim.sound_circuit
#print axioms XSim.stationary
#print axioms XSim.win_exact
#print axioms XSim.Demo.fp_q_concrete
#print axioms XSim.Demo.hz_q_abs
#print axioms XSim.Demo.hz_nondeterministic
#print axioms DelaySAF.saf_eq_delay_iff
#print axioms DelaySAF.saf_transport
#print axioms DelaySAF.saf_not_transport
#print axioms DelaySAF.saf_runt_not_inertial
#print axioms DelaySAF.saf_pulse_eq_inertial
#print axioms DelaySAF.chain_settle_le_delay
#print axioms DelaySAF.xor_settle_late
#print axioms DelaySAF.net_eq_delay_of_spaced
#print axioms LutAudit.audit_bd_arbiter_ustate_O6
#print axioms LutAudit.audit_bd_c4_u_O
#print axioms LutAudit.celem_same_direction_hazard_free
#print axioms LutAudit.lut_static_glitch_free
#print axioms LutAudit.dyn_single_window
#print axioms LutAudit.arb_grant_near_tie_runt
#print axioms ArbHeldTimed2.nonvacuous
#print axioms ArbHeldTimed2.rt1_exclusion2
#print axioms ArbHeldTimed2.rt2_exclusion2_arcs
#print axioms ArbHeldTimed2.prj_pulse2_tight
#print axioms ArbHeldTimed2.A1_runt_overlap
#print axioms ArbHeldTimed.rt1_exclusion
#print axioms ArbHeldTimed.rt2_exclusion_arcs
#print axioms ArbHeldTimed.prj_arc_only
#print axioms LibCtlMergeMux.j0_spec
#print axioms LibCtlMergeMux.mux_joins_excl_K
#print axioms LibCtlMergeMux.j0_hazard_x_up_c_down
#print axioms LibEndMemMlink.db_eq
#print axioms LibEndMemMlink.singleX_all
#print axioms LibEndMemMlink.mlink_req_bit_H
#print axioms LibEndMemMlink.flink_req_bit_H
#print axioms LibEndMemMlink.mlink_runt_reach
#print axioms LibEndMemMlink.masks_fail_without_H
#print axioms ArbBinary.exclusion_transport
#print axioms ArbBinary.arbiter_exclusion
#print axioms ArbBinary.runt_overlap
#print axioms TernaryPhases.phases_sound
#print axioms TernaryPhases.arb_a0_fall_skewed_early_ack
#print axioms TernaryPhases.cel_x_exact
#print axioms TernaryPhases.arb_tie_exact
#print axioms MuxTree.muxTree_eq_lutK
#print axioms MuxTree.Tree.evalK_order_indep
#print axioms MuxTree.build_evalK_eq_lutK
