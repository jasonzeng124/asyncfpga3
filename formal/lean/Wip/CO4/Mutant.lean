import Formal.Net.CellBindOps

/-!
# CO4 negative control (EXPECTED TO FAIL): the binding proof on a mutated INIT

`f2_gate` of `CellBindOps` (the generated bd_fork N = 2 acknowledge LUT is the C-element),
re-run verbatim on the netlist with ONE INIT bit flipped (bit 1: `a0 = 1, a1 = 0, q = 0`).
`decide +kernel` must reject it; this file must NOT check. Run:

    cd formal && ./slot.sh lake env lean Wip/CO4/Mutant.lean     # expect an error at f2_gate_mut

Every other `*_gate` lemma (f3..f6t, j2, uor, the chain stages, link, steer, mux, arbiter acks)
has the same shape, so flipping any INIT bit that the lemma's function depends on breaks
the build of `CellBindOps` (and of `OpsGen`), hence of `CellBindGcd`.
-/

namespace Formal.Net.CellBind.Mutant
open Formal.Gen Formal.Gen.Cells Formal.Net.Ops.Gen Formal.Net.CellBind.Ops

def mutFork : Netlist :=
  { bd_fork_N2 with cells := bd_fork_N2.cells.map (fun c => { c with init := c.init ^^^ 2 }) }

def f2mF (p : Bool × Bool) (q : Bool) : Bool :=
  genF mutFork forkCell .O ["ack_in[0]", "ack_in[1]", "ack", "rst"] [p.1, p.2, q, false]

theorem f2_gate_mut : ∀ (p : Bool × Bool) q, f2mF p q = cel2 p.1 p.2 q := by
  intro ⟨a, b⟩ q; revert a b q; decide +kernel

end Formal.Net.CellBind.Mutant
