import Formal.Gen.Cells
import Formal.Gen.PrelimSem
import Formal.Cells.CElemFn
import Formal.Cells.CTree
import Formal.Cells.CElemTiming
import Formal.Core.Lut
import Formal.Core.LutCells
open Formal.Core.LutList

/-!
# 11d: generated C-elements (`bd_ce.v`), C-trees, fork and join (`bd_ctl.v`)

Every netlist here is GENERATED (`Formal.Gen.Cells.*`, from yosys 0.62
`synth_xilinx -noiopad`, see `formal/tools/gen/gen.sh`). Nothing about a cell
below is typed by hand except the specification it is compared with.

For each cell, three kinds of statement, all `decide +kernel`:
* `*_lut`: the cell's kind, INIT and pin -> net map are exactly shard B's
  transcription (B's INIT constant, B's pin order). A changed INIT or pin in
  `cells/rtl/` changes `Cells.lean` (gen.sh --check fails), and then this fails.
* `*_gate_B` / `*_gate_K`: the generated gate, read binary / Kleene, IS B's
  cell function (`c2B`, `c2K`, ...), as a function of the values on its nets.
* `*_next_*`: 11a's unit-step reading of the whole netlist (feedback nets as
  state) equals B's specification (`cSpec` with reset polarity).
Plus cross-checks against the other INIT constants in the tree: shard B's
`CTree`, `CElemTiming`, and shard A's `Formal.Core.Lut` (`Init.*`, BitVec) and
`Formal.Core.LutCells` (A's regex extraction of the Verilog).

Hypotheses: H_KLEENE_LUT for every `_K` theorem (as in B); the unit-step
reading for `_next_` (feedback read as an independent input, B's reading).
-/

namespace Formal.Gen.ProofsCE
open Formal.Cells Formal.Gen Formal.Gen.Cells
open Formal.Cells.CElemFn (cSpec clr set c2B c2setB c2nB c2nsetB c3B c4B c2norstB c3norstB
  c2K c2setK c2nK c2nsetK c3K c4K c2norstK c3norstK INIT_c2 INIT_c2_set INIT_c2n INIT_c2n_set
  INIT_c3 INIT_c4 INIT_c2_norst INIT_c3_norst)

/-! ## The eight C-element LUTs: INIT and pins = B's transcription -/

theorem bd_c2_lut : bd_c2.lutIs "u" (.lut 6) INIT_c2 ["a", "b", "q", "rst", "0", "0"] ["q"] := by
  decide +kernel
theorem bd_c2_set_lut :
    bd_c2_set.lutIs "u" (.lut 6) INIT_c2_set ["a", "b", "q", "rst", "0", "0"] ["q"] := by
  decide +kernel
theorem bd_c2n_lut : bd_c2n.lutIs "u" (.lut 6) INIT_c2n ["a", "b", "q", "rst", "0", "0"] ["q"] := by
  decide +kernel
theorem bd_c2n_set_lut :
    bd_c2n_set.lutIs "u" (.lut 6) INIT_c2n_set ["a", "b", "q", "rst", "0", "0"] ["q"] := by
  decide +kernel
theorem bd_c3_lut : bd_c3.lutIs "u" (.lut 6) INIT_c3 ["a", "b", "c", "q", "rst", "0"] ["q"] := by
  decide +kernel
theorem bd_c4_lut : bd_c4.lutIs "u" (.lut 6) INIT_c4 ["a", "b", "c", "d", "q", "rst"] ["q"] := by
  decide +kernel
theorem bd_c2_norst_lut :
    bd_c2_norst.lutIs "u" (.lut 6) INIT_c2_norst ["a", "b", "q", "0", "0", "0"] ["q"] := by
  decide +kernel
theorem bd_c3_norst_lut :
    bd_c3_norst.lutIs "u" (.lut 6) INIT_c3_norst ["a", "b", "c", "q", "0", "0"] ["q"] := by
  decide +kernel

/-! ## Gate functions = B's binary and Kleene cell functions -/

theorem bd_c2_gate_B : ∀ a b q rst : Bool,
    bd_c2.gateN boolSem "u" .O [("a", a), ("b", b), ("q", q), ("rst", rst)] = some (c2B a b q rst) := by
  decide +kernel
theorem bd_c2_gate_K : ∀ a b q rst : K3,
    bd_c2.gateN kleeneSemP "u" .O [("a", a), ("b", b), ("q", q), ("rst", rst)] = some (c2K a b q rst) := by
  decide +kernel
theorem bd_c2_set_gate_B : ∀ a b q rst : Bool,
    bd_c2_set.gateN boolSem "u" .O [("a", a), ("b", b), ("q", q), ("rst", rst)] =
      some (c2setB a b q rst) := by decide +kernel
theorem bd_c2_set_gate_K : ∀ a b q rst : K3,
    bd_c2_set.gateN kleeneSemP "u" .O [("a", a), ("b", b), ("q", q), ("rst", rst)] =
      some (c2setK a b q rst) := by decide +kernel
theorem bd_c2n_gate_B : ∀ a b q rst : Bool,
    bd_c2n.gateN boolSem "u" .O [("a", a), ("b", b), ("q", q), ("rst", rst)] =
      some (c2nB a b q rst) := by decide +kernel
theorem bd_c2n_gate_K : ∀ a b q rst : K3,
    bd_c2n.gateN kleeneSemP "u" .O [("a", a), ("b", b), ("q", q), ("rst", rst)] =
      some (c2nK a b q rst) := by decide +kernel
theorem bd_c2n_set_gate_B : ∀ a b q rst : Bool,
    bd_c2n_set.gateN boolSem "u" .O [("a", a), ("b", b), ("q", q), ("rst", rst)] =
      some (c2nsetB a b q rst) := by decide +kernel
theorem bd_c2n_set_gate_K : ∀ a b q rst : K3,
    bd_c2n_set.gateN kleeneSemP "u" .O [("a", a), ("b", b), ("q", q), ("rst", rst)] =
      some (c2nsetK a b q rst) := by decide +kernel
theorem bd_c3_gate_B : ∀ a b c q rst : Bool,
    bd_c3.gateN boolSem "u" .O [("a", a), ("b", b), ("c", c), ("q", q), ("rst", rst)] =
      some (c3B a b c q rst) := by decide +kernel
theorem bd_c3_gate_K : ∀ a b c q rst : K3,
    bd_c3.gateN kleeneSemP "u" .O [("a", a), ("b", b), ("c", c), ("q", q), ("rst", rst)] =
      some (c3K a b c q rst) := by decide +kernel
theorem bd_c4_gate_B : ∀ a b c d q rst : Bool,
    bd_c4.gateN boolSem "u" .O [("a", a), ("b", b), ("c", c), ("d", d), ("q", q), ("rst", rst)] =
      some (c4B a b c d q rst) := by decide +kernel
theorem bd_c4_gate_K : ∀ a b c d q rst : K3,
    bd_c4.gateN kleeneSemP "u" .O [("a", a), ("b", b), ("c", c), ("d", d), ("q", q), ("rst", rst)] =
      some (c4K a b c d q rst) := by decide +kernel
theorem bd_c2_norst_gate_B : ∀ a b q : Bool,
    bd_c2_norst.gateN boolSem "u" .O [("a", a), ("b", b), ("q", q)] = some (c2norstB a b q) := by
  decide +kernel
theorem bd_c2_norst_gate_K : ∀ a b q : K3,
    bd_c2_norst.gateN kleeneSemP "u" .O [("a", a), ("b", b), ("q", q)] = some (c2norstK a b q) := by
  decide +kernel
theorem bd_c3_norst_gate_B : ∀ a b c q : Bool,
    bd_c3_norst.gateN boolSem "u" .O [("a", a), ("b", b), ("c", c), ("q", q)] =
      some (c3norstB a b c q) := by decide +kernel
theorem bd_c3_norst_gate_K : ∀ a b c q : K3,
    bd_c3_norst.gateN kleeneSemP "u" .O [("a", a), ("b", b), ("c", c), ("q", q)] =
      some (c3norstK a b c q) := by decide +kernel

/-! ## Unit-step reading of each whole netlist = B's specification

Interface first: the generated port and state order the step theorems use. -/

theorem ce_iface :
    bd_c2.inputNames = ["a", "b", "rst"] ∧ bd_c2.stateNames = ["q"] ∧ bd_c2.outputNames = ["q"] ∧
    bd_c2_set.inputNames = ["a", "b", "rst"] ∧ bd_c2n.inputNames = ["a", "b", "rst"] ∧
    bd_c2n_set.inputNames = ["a", "b", "rst"] ∧ bd_c3.inputNames = ["a", "b", "c", "rst"] ∧
    bd_c4.inputNames = ["a", "b", "c", "d", "rst"] ∧ bd_c2_norst.inputNames = ["a", "b"] ∧
    bd_c3_norst.inputNames = ["a", "b", "c"] := by decide +kernel

theorem bd_c2_next : ∀ a b rst q : Bool,
    bd_c2.next boolSem [a, b, rst] [q] = some [clr rst (cSpec [a, b] q)] := by decide +kernel
theorem bd_c2_outs : ∀ a b rst q : Bool, bd_c2.outs boolSem [a, b, rst] [q] = some [q] := by
  decide +kernel
theorem bd_c2_set_next : ∀ a b rst q : Bool,
    bd_c2_set.next boolSem [a, b, rst] [q] = some [set rst (cSpec [a, b] q)] := by decide +kernel
theorem bd_c2n_next : ∀ a b rst q : Bool,
    bd_c2n.next boolSem [a, b, rst] [q] = some [clr rst (cSpec [a, !b] q)] := by decide +kernel
theorem bd_c2n_set_next : ∀ a b rst q : Bool,
    bd_c2n_set.next boolSem [a, b, rst] [q] = some [set rst (cSpec [a, !b] q)] := by decide +kernel
theorem bd_c3_next : ∀ a b c rst q : Bool,
    bd_c3.next boolSem [a, b, c, rst] [q] = some [clr rst (cSpec [a, b, c] q)] := by decide +kernel
theorem bd_c4_next : ∀ a b c d rst q : Bool,
    bd_c4.next boolSem [a, b, c, d, rst] [q] = some [clr rst (cSpec [a, b, c, d] q)] := by
  decide +kernel
theorem bd_c2_norst_next : ∀ a b q : Bool,
    bd_c2_norst.next boolSem [a, b] [q] = some [cSpec [a, b] q] := by decide +kernel
theorem bd_c3_norst_next : ∀ a b c q : Bool,
    bd_c3_norst.next boolSem [a, b, c] [q] = some [cSpec [a, b, c] q] := by decide +kernel
/-- Kleene, whole netlist (all 3^4 inputs), against B's `c2K`. -/
theorem bd_c2_next_K : ∀ a b rst q : K3,
    bd_c2.next kleeneSemP [a, b, rst] [q] = some [c2K a b q rst] := by decide +kernel
theorem bd_c4_next_K : ∀ a b c d rst q : K3,
    bd_c4.next kleeneSemP [a, b, c, d, rst] [q] = some [c4K a b c d q rst] := by decide +kernel

/-! ## Cross-checks with the other INIT constants in the tree -/

theorem ce_inits_B :
    bd_c2.initOf "u" = some Formal.Cells.CTree.INIT_C2 ∧
    bd_c3.initOf "u" = some Formal.Cells.CTree.INIT_C3 ∧
    bd_c4.initOf "u" = some Formal.Cells.CTree.INIT_C4 ∧
    bd_c2.initOf "u" = some Formal.Cells.CElemTiming.INIT_c2 ∧
    bd_c2_set.initOf "u" = some Formal.Cells.CElemTiming.INIT_c2_set ∧
    bd_c2n.initOf "u" = some Formal.Cells.CElemTiming.INIT_c2n := by decide +kernel

/-- Shard A's `Formal.Core.Lut.Init` (BitVec INITs). -/
theorem ce_inits_core :
    bd_c2.initOf "u" = some Formal.Core.Init.bd_c2.init.toNat ∧
    bd_c2_set.initOf "u" = some Formal.Core.Init.bd_c2_set.init.toNat ∧
    bd_c2n.initOf "u" = some Formal.Core.Init.bd_c2n.init.toNat ∧
    bd_c2n_set.initOf "u" = some Formal.Core.Init.bd_c2n_set.init.toNat ∧
    bd_c3.initOf "u" = some Formal.Core.Init.bd_c3.init.toNat ∧
    bd_c4.initOf "u" = some Formal.Core.Init.bd_c4.init.toNat ∧
    bd_c2_norst.initOf "u" = some Formal.Core.Init.bd_c2_norst.init.toNat ∧
    bd_c3_norst.initOf "u" = some Formal.Core.Init.bd_c3_norst.init.toNat := by decide +kernel

/-- The generated gate equals shard A's Core reading of its own INIT
(`Lut.eval` on BitVec, `Formal.Core.Lut`). -/
theorem bd_c2_gate_core : ∀ a b q rst : Bool,
    bd_c2.gateN boolSem "u" .O [("a", a), ("b", b), ("q", q), ("rst", rst)] =
      some (Formal.Core.Init.bd_c2.eval (Formal.Core.bvec [a, b, q, rst, false, false] 6)) := by
  decide +kernel
theorem bd_c4_gate_core : ∀ a b c d q rst : Bool,
    bd_c4.gateN boolSem "u" .O [("a", a), ("b", b), ("c", c), ("d", d), ("q", q), ("rst", rst)] =
      some (Formal.Core.Init.bd_c4.eval (Formal.Core.bvec [a, b, c, d, q, rst] 6)) := by
  decide +kernel

/-- Shard A's regex extraction `Formal.Core.LutCells` agrees with yosys. -/
theorem ce_inits_lutcells :
    bd_c2.initOf "u" = some Formal.Core.LutCells.bd_c2_u.init ∧
    bd_c2_set.initOf "u" = some Formal.Core.LutCells.bd_c2_set_u.init ∧
    bd_c2n.initOf "u" = some Formal.Core.LutCells.bd_c2n_u.init ∧
    bd_c2n_set.initOf "u" = some Formal.Core.LutCells.bd_c2n_set_u.init ∧
    bd_c3.initOf "u" = some Formal.Core.LutCells.bd_c3_u.init ∧
    bd_c4.initOf "u" = some Formal.Core.LutCells.bd_c4_u.init ∧
    bd_c2_norst.initOf "u" = some Formal.Core.LutCells.bd_c2_norst_u.init ∧
    bd_c3_norst.initOf "u" = some Formal.Core.LutCells.bd_c3_norst_u.init := by decide +kernel

/-! ## `bd_ctree`: the generate block, as synthesized

N = 1 is a wire; N = 3 is one `bd_c3`; N = 5 and N = 8 are B's `CTree.t5` /
`CTree.t8` (= `CTree.gen 5`, `gen 8` by B's `gen5`, `gen8`): chunks of four
under a `bd_c2`, here read off the generated netlist cell by cell. -/

def T5_C4 : String := "genblk1.genblk1.genblk1.gt.chunk[0].u.genblk1.genblk1.genblk1.g4.u.u"
def T8_C4b : String := "genblk1.genblk1.genblk1.gt.chunk[1].u.genblk1.genblk1.genblk1.g4.u.u"
def T_TOP : String := "genblk1.genblk1.genblk1.gt.utop.genblk1.g2.u.u"
def P0 : String := "genblk1.genblk1.genblk1.gt.part[0]"
def P1 : String := "genblk1.genblk1.genblk1.gt.part[1]"

theorem bd_ctree_N1_wire : ∀ a rst : Bool, bd_ctree_N1.outs boolSem [a, rst] [] = some [a] ∧
    bd_ctree_N1.cells.isEmpty = true := by decide +kernel

theorem bd_ctree_N3_lut :
    bd_ctree_N3.lutIs "genblk1.genblk1.g3.u.u" (.lut 6) INIT_c3
      ["a[0]", "a[1]", "a[2]", "q", "rst", "0"] ["q"] := by decide +kernel

/-- `t5 = C2(C4(a0..a3), a4)`: exactly two cells, B's INITs and B's pins. -/
theorem bd_ctree_N5_shape :
    bd_ctree_N5.cellNames = [T5_C4, T_TOP] ∧
    bd_ctree_N5.lutIs T5_C4 (.lut 6) INIT_c4 ["a[0]", "a[1]", "a[2]", "a[3]", P0, "rst"] [P0] ∧
    bd_ctree_N5.lutIs T_TOP (.lut 6) INIT_c2 [P0, "a[4]", "q", "rst", "0", "0"] ["q"] := by
  decide +kernel

theorem bd_ctree_N8_shape :
    bd_ctree_N8.cellNames = [T5_C4, T8_C4b, T_TOP] ∧
    bd_ctree_N8.lutIs T5_C4 (.lut 6) INIT_c4 ["a[0]", "a[1]", "a[2]", "a[3]", P0, "rst"] [P0] ∧
    bd_ctree_N8.lutIs T8_C4b (.lut 6) INIT_c4 ["a[4]", "a[5]", "a[6]", "a[7]", P1, "rst"] [P1] ∧
    bd_ctree_N8.lutIs T_TOP (.lut 6) INIT_c2 [P0, P1, "q", "rst", "0", "0"] ["q"] := by
  decide +kernel

/-- Unit step of the N = 5 tree, state `[q, part[0]]`: each node is B's
`c2r`/`c4r` (`CTree`) on its children, i.e. one step of `CTree.t5`. -/
theorem bd_ctree_N5_next : ∀ a0 a1 a2 a3 a4 rst q p0 : Bool,
    bd_ctree_N5.next boolSem [a0, a1, a2, a3, a4, rst] [q, p0] =
      some [Formal.Cells.CTree.c2r rst p0 a4 q, Formal.Cells.CTree.c4r rst a0 a1 a2 a3 p0] := by
  decide +kernel

theorem bd_ctree_N8_next : ∀ a0 a1 a2 a3 a4 a5 a6 a7 rst q p0 p1 : Bool,
    bd_ctree_N8.next boolSem [a0, a1, a2, a3, a4, a5, a6, a7, rst] [q, p0, p1] =
      some [Formal.Cells.CTree.c2r rst p0 p1 q, Formal.Cells.CTree.c4r rst a0 a1 a2 a3 p0,
            Formal.Cells.CTree.c4r rst a4 a5 a6 a7 p1] := by
  decide +kernel

/-! ## `bd_fork`, `bd_join`: the rendezvous plus wires -/

theorem fork_join_iface :
    bd_fork_N2.inputNames = ["rst", "req", "ack_in[0]", "ack_in[1]"] ∧
    bd_fork_N2.outputNames = ["ack", "req_out[0]", "req_out[1]"] ∧
    bd_join_N3.inputNames = ["rst", "req_in[0]", "req_in[1]", "req_in[2]", "ack"] ∧
    bd_join_N3.outputNames = ["ack_out[0]", "ack_out[1]", "ack_out[2]", "req"] := by decide +kernel

/-- Fork, N = 2: `ack = C(ack_in[0], ack_in[1])` (B's `c2B`), `req` broadcast. -/
theorem bd_fork_N2_spec : ∀ rst req a0 a1 q : Bool,
    bd_fork_N2.next boolSem [rst, req, a0, a1] [q] = some [c2B a0 a1 q rst] ∧
    bd_fork_N2.outs boolSem [rst, req, a0, a1] [q] = some [q, req, req] := by decide +kernel

/-- Join, N = 3: `req = C3(req_in)` (B's `c3B`), `ack` broadcast. -/
theorem bd_join_N3_spec : ∀ rst r0 r1 r2 ack q : Bool,
    bd_join_N3.next boolSem [rst, r0, r1, r2, ack] [q] = some [c3B r0 r1 r2 q rst] ∧
    bd_join_N3.outs boolSem [rst, r0, r1, r2, ack] [q] = some [ack, ack, ack, q] := by decide +kernel

theorem bd_join_N2_lut :
    bd_join_N2.lutIs "u.genblk1.g2.u.u" (.lut 6) INIT_c2
      ["req_in[0]", "req_in[1]", "req", "rst", "0", "0"] ["req"] := by decide +kernel

/-- Fork, N = 5: the same tree as `bd_ctree_N5` over the acknowledges. -/
theorem bd_fork_N5_shape :
    bd_fork_N5.lutIs ("u." ++ T5_C4) (.lut 6) INIT_c4
      ["ack_in[0]", "ack_in[1]", "ack_in[2]", "ack_in[3]", "u." ++ P0, "rst"] ["u." ++ P0] ∧
    bd_fork_N5.lutIs ("u." ++ T_TOP) (.lut 6) INIT_c2
      ["u." ++ P0, "ack_in[4]", "ack", "rst", "0", "0"] ["ack"] := by decide +kernel

end Formal.Gen.ProofsCE
