import Formal.Cells.CElemFn
import Formal.Cells.CElemTiming
import Formal.Cells.CTree
import Formal.Cells.Latch
import Formal.Cells.LinkHandshake
import Formal.Cells.LinkTimed
import Formal.Cells.Bundling
import Formal.Cells.ArbKleene
import Formal.Cells.ArbHandover
import Formal.Cells.ArbA0Fork
import Formal.Cells.TernarySound
open Formal.Cells
#print axioms CElemFn.c2_spec
#print axioms CElemFn.c4_spec
#print axioms CElemTiming.c2_follow_hold
#print axioms CElemTiming.runt_oscillates
#print axioms CElemTiming.c2_four_phase
#print axioms CTree.reachable_eq_flat
#print axioms CTree.ctree_eq_flat
#print axioms CTree.cex_noAck5
#print axioms Latch.holds_value
#print axioms Latch.link_latch_holds
#print axioms Latch.hold_of_dack
#print axioms LinkHandshake.conservation
#print axioms LinkHandshake.bounded
#print axioms LinkHandshake.deadlock_free
#print axioms LinkHandshake.setup_iff
#print axioms LinkHandshake.pipe_data
#print axioms LinkHandshake.di_pipe3
#print axioms Bundling.capture
#print axioms Bundling.counter_rule_I
#print axioms Bundling.ff_counter_ruleF
#print axioms ArbKleene.kleene_exclusion
#print axioms ArbKleene.grant_pairs
#print axioms ArbHandover.header_16ps
#print axioms ArbHandover.overlap_duration_r2_to_r1
#print axioms ArbHandover.held_protocol
#print axioms ArbHandover.overlap_skew_r2_to_r1_le
#print axioms ArbA0Fork.client2_iff
#print axioms ArbA0Fork.client1_iff
#print axioms ArbA0Fork.client2_box
#print axioms ArbA0Fork.run_exists
#print axioms LinkTimed.stage_token
#print axioms LinkTimed.stage_forward
#print axioms TernarySound.A_invariant
#print axioms TernarySound.algB_bounded
#print axioms TernarySound.arb_runt_opposite
#print axioms TernarySound.arb_acks_quiet
