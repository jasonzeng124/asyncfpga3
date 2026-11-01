import Formal.Target.Net.All
import Formal.Target.WitBoundary
import Formal.Target.WitSlice
import Formal.Cells.ArbClean
import Formal.Cells.ArbOKRepair

/-! Audit T5: axioms of every headline theorem of the committed decoded-net data and of Witness /
WitBoundary / WitSlice (formal 6f094d32), plus kernel checks tying `arbs` to the decoded gates. -/

open Formal.Target Formal.Target.Decoded Formal.Target.Wit

#print axioms Formal.Target.Decoded.net_wf
#print axioms Formal.Target.Decoded.gates_wf
#print axioms Formal.Target.Decoded.gates_outs
#print axioms Formal.Target.Decoded.g000_wf
#print axioms Formal.Target.Decoded.g079_outs
#print axioms Formal.Target.Net.wf_of_outs
#print axioms Formal.Target.Wit.chkFrom_sound
#print axioms Formal.Target.Wit.eq_ext
#print axioms Formal.Target.Wit.gateOK_slow
#print axioms Formal.Target.Wit.chkPer_sound
#print axioms Formal.Target.Wit.perOn_of_chk
#print axioms Formal.Target.Wit.adm_slow
#print axioms Formal.Target.Wit.start_slow
#print axioms Formal.Target.Wit.flip_iff
#print axioms Formal.Target.Wit.rises_eq
#print axioms Formal.Target.Wit.walk_sound
#print axioms Formal.Target.Wit.arbOK_one
#print axioms Formal.Target.Wit.envIn_of
#print axioms Formal.Target.Wit.envOut_of
#print axioms Formal.Target.Wit.envIn_congr
#print axioms Formal.Target.Wit.envOut_congr
#print axioms Formal.Target.Wit.ext_eq_val
#print axioms Formal.Target.Wit.forall_drop_take
#print axioms Formal.Target.Wit.forall_drop_len

/-- The statement the witness machinery aims at uses the Spec's own `NetCorrect` on the committed data. -/
example : Prop := ¬ NetCorrect net boundary arbs Wit.pSlow 656 20000 0 2999

/-- `net_wf` is about exactly the net with 200097 nodes. -/
example : net.n = 200097 := rfl

/-- Kernel check: for each listed arbiter, the gate at index q drives q, is a 6-input gate, and every
listed input is one of that gate's pins (so `arbs` names the inputs of the gate that drives q). -/
theorem arbs_on_gates : (arbs.all fun a =>
    let g := gates.getD a.q default
    g.out == a.q && g.k == 6 && a.ins.length == 5 && a.ins.all (fun n => g.ins.contains n)) = true := by
  decide +kernel

#print axioms arbs_on_gates

-- B's ArbClean (6603bdd1, f4a4ef64): headline theorems
#print axioms Formal.Cells.ArbClean.q_clean_set
#print axioms Formal.Cells.ArbClean.q_clean_reset
#print axioms Formal.Cells.ArbClean.q_clean_set_gen
#print axioms Formal.Cells.ArbClean.targetQ_facts
#print axioms Formal.Cells.ArbClean.targetQ_swap_fails
#print axioms Formal.Cells.ArbOKRepair.arbOK_admits_handover
#print axioms Formal.Cells.ArbOKRepair.arbOK_needs_T_ge_arc
