import Formal.Net.Import.Cells
import Formal.Cells.CElemFn
import Formal.Cells.Latch
import Formal.Cells.ArbKleene

/-!
# Track 11a: the imported netlists equal the cell specifications

Every netlist below is the GENERATED `Formal.Net.Import.Gen.*` value: what
yosys 0.62 `synth_xilinx` (the project's flow) left of each library cell,
read from `write_json` by `formal/tools/import/yosys2lean.py`. No INIT and no
pin map in this file is typed by hand.

Each theorem says: one combinational step of the imported netlist, with its
feedback nets as state (`Netlist.next`), equals

* the specification (`cSpec` with reset polarity, `bmux`, ...) of shard B's
  `Formal/Cells/` files, binary, and
* shard B's own hand-transcribed cell function (`c2B`, `c2K`, `qArbK`, ...),
  binary and Kleene.

The second form is the point of the import: every theorem shard B proved about
its transcription (glitch freedom, X containment, Kleene exclusion, ...)
transfers to the synthesized netlist by rewriting; `arbiter_kleene_exclusion`
below does exactly that for the arbiter.

Hypotheses in force (all in the semantics, see `Netlist.lean`):
* H_KLEENE_LUT (Kleene theorems only) as in `Formal.Cells.Prelim`;
* H_PAD_IDENTITY: the IBUF/OBUF that `synth_xilinx` adds at a top level are
  zero-delay wires (they do not exist when the cell is used inside a design);
* the unit-step reading: `next` is the loop's next-state function with the
  feedback pin read as an independent input (B's reading; the feedback wire's
  delay is not modelled here).
All proofs are `decide` (kernel evaluation of the interpreter on the imported
data); no native code.
-/

namespace Formal.Net.Import.Proofs
open Formal.Cells Formal.Net.Import Formal.Net.Import.Gen
open Formal.Cells.CElemFn (cSpec clr set c2B c2setB c2nB c2nsetB c3B c4B c2K c2setK c2nK c2nsetK)
open Formal.Cells.Latch (bmux PAIR)
open Formal.Cells.ArbKleene (g1K g2K qArbK r0K qCellK cK kleene_exclusion)

/-! ## Interface: the generated port and state order the theorems rely on

If a regenerated netlist reorders ports or cuts a different feedback net,
these fail before anything else does. -/

theorem bd_c2_iface :
    bd_c2.inputNames = ["a", "b", "rst"] ∧ bd_c2.outputNames = ["q"] ∧
    bd_c2.stateNames = ["$iopadmap$q"] := by decide +kernel
theorem bd_c3_iface : bd_c3.inputNames = ["a", "b", "c", "rst"] := by decide +kernel
theorem bd_c4_iface : bd_c4.inputNames = ["a", "b", "c", "d", "rst"] := by decide +kernel
theorem bd_latch_W3_iface :
    bd_latch_W3.inputNames = ["d[0]", "d[1]", "d[2]", "en"] ∧
    bd_latch_W3.stateNames = ["$iopadmap$q[0]", "$iopadmap$q[1]", "$iopadmap$q[2]"] := by
  decide +kernel
theorem bd_arbiter_iface :
    bd_arbiter.inputNames = ["rst", "r1", "r2", "A0"] ∧
    bd_arbiter.outputNames = ["A1", "A2", "R0", "g1", "g2"] ∧
    bd_arbiter.stateNames = ["ua1.q", "ua2.q", "q"] := by decide +kernel

/-! ## `bd_ce.v`: the C-elements -/

/-- **The headline of probe 11a.** The synthesized `bd_c2`'s next state is
`~rst . C(a, b)` with `q` held (B's `c2_spec`). -/
theorem bd_c2_next_spec : ∀ a b rst q : Bool,
    bd_c2.next boolSem [a, b, rst] [q] = some [clr rst (cSpec [a, b] q)] := by decide +kernel

/-- With reset low it is exactly majority(a, b, q) (`bd_ce.v` header). -/
theorem bd_c2_next_maj : ∀ a b q : Bool,
    bd_c2.next boolSem [a, b, false] [q] = some [(a && b) || (a && q) || (b && q)] := by
  decide +kernel

/-- The output port shows the state (through the OBUF). -/
theorem bd_c2_outs : ∀ a b rst q : Bool, bd_c2.outs boolSem [a, b, rst] [q] = some [q] := by
  decide +kernel

theorem bd_c2_next_B : ∀ a b rst q : Bool,
    bd_c2.next boolSem [a, b, rst] [q] = some [c2B a b q rst] := by decide +kernel
theorem bd_c2_next_K : ∀ a b rst q : K3,
    bd_c2.next kleeneSem [a, b, rst] [q] = some [c2K a b q rst] := by decide +kernel

theorem bd_c2_set_next_spec : ∀ a b rst q : Bool,
    bd_c2_set.next boolSem [a, b, rst] [q] = some [set rst (cSpec [a, b] q)] := by decide +kernel
theorem bd_c2_set_next_K : ∀ a b rst q : K3,
    bd_c2_set.next kleeneSem [a, b, rst] [q] = some [c2setK a b q rst] := by decide +kernel

theorem bd_c2n_next_spec : ∀ a b rst q : Bool,
    bd_c2n.next boolSem [a, b, rst] [q] = some [clr rst (cSpec [a, !b] q)] := by decide +kernel
theorem bd_c2n_next_K : ∀ a b rst q : K3,
    bd_c2n.next kleeneSem [a, b, rst] [q] = some [c2nK a b q rst] := by decide +kernel

theorem bd_c2n_set_next_spec : ∀ a b rst q : Bool,
    bd_c2n_set.next boolSem [a, b, rst] [q] = some [set rst (cSpec [a, !b] q)] := by decide +kernel
theorem bd_c2n_set_next_K : ∀ a b rst q : K3,
    bd_c2n_set.next kleeneSem [a, b, rst] [q] = some [c2nsetK a b q rst] := by decide +kernel

theorem bd_c3_next_spec : ∀ a b c rst q : Bool,
    bd_c3.next boolSem [a, b, c, rst] [q] = some [clr rst (cSpec [a, b, c] q)] := by decide +kernel
theorem bd_c4_next_spec : ∀ a b c d rst q : Bool,
    bd_c4.next boolSem [a, b, c, d, rst] [q] = some [clr rst (cSpec [a, b, c, d] q)] := by
  decide +kernel

/-! ## `bd_latch.v` -/

/-- W = 3: one fractured `LUT6_2` pair (bits 0, 1) and one odd `LUT6` (bit 2).
Every bit is a transparent-high latch. -/
theorem bd_latch_W3_next_spec : ∀ d0 d1 d2 en q0 q1 q2 : Bool,
    bd_latch_W3.next boolSem [d0, d1, d2, en] [q0, q1, q2] =
      some [bmux en d0 q0, bmux en d1 q1, bmux en d2 q2] := by decide +kernel

/-- W = 2, Kleene: each bit is `K3.mux en q d` (B's `pair_o5_kleene`,
`pair_o6_kleene`): X on one bit's pins never reaches the other bit. -/
theorem bd_latch_W2_next_K : ∀ d0 d1 en q0 q1 : K3,
    bd_latch_W2.next kleeneSem [d0, d1, en] [q0, q1] =
      some [K3.mux en q0 d0, K3.mux en q1 d1] := by decide +kernel

theorem bd_latch_rst_W1_next_spec : ∀ d en rst q : Bool,
    bd_latch_rst_W1.next boolSem [d, en, rst] [q] =
      some [if rst then false else bmux en d q] := by decide +kernel

/-! ## `bd_arb.v` -/

theorem bd_arbcell_next_K : ∀ r1 r2 rst q : K3,
    bd_arbcell.next kleeneSem [r1, r2, rst] [q] = some [qCellK r1 r2 q rst] := by decide +kernel
theorem bd_arbcell_outs_K : ∀ r1 r2 rst q : K3,
    bd_arbcell.outs kleeneSem [r1, r2, rst] [q] = some [g1K r1 r2 q, g2K r1 r2 q] := by decide +kernel

/-- The arbiter's three loops (state `[A1, A2, q]`), binary, against the
equations of `bd_arb.v`'s header: `q = rst + (A0 ? q : C(r1, ~r2))`, and each
acknowledge `A_i = ~rst . C(g_i, A0)` with `g1 = r1.q`, `g2 = r2.~q`. -/
theorem bd_arbiter_next_spec : ∀ rst r1 r2 a0 a1 a2 q : Bool,
    bd_arbiter.next boolSem [rst, r1, r2, a0] [a1, a2, q] =
      some [clr rst (cSpec [r1 && q, a0] a1),
            clr rst (cSpec [r2 && !q, a0] a2),
            rst || (if a0 then q else ((r1 && !r2) || (q && (r1 || !r2))))] := by decide +kernel

theorem bd_arbiter_outs_spec : ∀ rst r1 r2 a0 a1 a2 q : Bool,
    bd_arbiter.outs boolSem [rst, r1, r2, a0] [a1, a2, q] =
      some [a1, a2, (r1 && q) || (r2 && !q), r1 && q, r2 && !q] := by decide +kernel

/-- Kleene, all 3^7 inputs: the synthesized arbiter is B's transcription. -/
theorem bd_arbiter_next_K : ∀ rst r1 r2 a0 a1 a2 q : K3,
    bd_arbiter.next kleeneSem [rst, r1, r2, a0] [a1, a2, q] =
      some [cK (g1K r1 r2 q) a0 a1 rst, cK (g2K r1 r2 q) a0 a2 rst, qArbK r1 r2 q rst a0] := by
  decide +kernel

theorem bd_arbiter_outs_K : ∀ rst r1 r2 a0 a1 a2 q : K3,
    bd_arbiter.outs kleeneSem [rst, r1, r2, a0] [a1, a2, q] =
      some [a1, a2, r0K r1 r2 q rst a0, g1K r1 r2 q, g2K r1 r2 q] := by decide +kernel

/-- Transfer of a shard-B theorem to the synthesized netlist: whatever the
(ternary) inputs and state, the imported arbiter's two grant ports are never
both a definite 1 (B's `kleene_exclusion`, H_KLEENE_LUT). -/
theorem arbiter_kleene_exclusion (rst r1 r2 a0 a1 a2 q : K3) (vs : List K3)
    (h : bd_arbiter.outs kleeneSem [rst, r1, r2, a0] [a1, a2, q] = some vs) :
    ¬ (vs[3]? = some .t ∧ vs[4]? = some .t) := by
  rw [bd_arbiter_outs_K] at h
  cases h
  simpa using kleene_exclusion r1 r2 q

end Formal.Net.Import.Proofs
