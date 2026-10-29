import Formal.Cells.LinkExact
import Formal.Cells.CTreeExact
open Formal.Cells
example : CElemFn.INIT_c2n = 0x00B200B200B200B2 := rfl
-- both sides of the LinkExact iff are inhabited, in scope (Wf ∧ Split):
example : ∀ v, Formal.Cells.LinkExact.SafeLink Formal.Cells.LinkExact.P0 v ∧
    ∀ i, Formal.Cells.LinkExact.Wf (Formal.Cells.LinkExact.Pv i) ∧
      Formal.Cells.LinkExact.Split (Formal.Cells.LinkExact.Pv i) ∧
      ¬ Formal.Cells.LinkExact.SafeLink (Formal.Cells.LinkExact.Pv i) v :=
  fun v => ⟨(Formal.Cells.LinkExact.witness v).2.2.2.1,
    fun i => ⟨Formal.Cells.LinkExact.Pv_wf i, Formal.Cells.LinkExact.Pv_split i,
      Formal.Cells.LinkExact.Pv_breaks v i⟩⟩
#print axioms Formal.Cells.LinkExact.exact
#print axioms Formal.Cells.LinkExact.no_cross
#print axioms Formal.Cells.LinkExact.witness
#print axioms Formal.Cells.LinkExact.Pv_breaks
#print axioms Formal.Cells.LinkExact.strict_edges
#print axioms Formal.Cells.CTreeExact.tree_box_exact
#print axioms Formal.Cells.CTreeExact.nonvacuous
#print axioms Formal.Cells.CTreeExact.sh6_glitch
#print axioms Formal.Cells.CTreeExact.sh6_numbers
