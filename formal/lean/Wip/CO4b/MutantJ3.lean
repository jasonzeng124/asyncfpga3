import Formal.Net.CellBindKOps
/-! NEGATIVE CONTROL (must NOT check): bd_join N = 3 with INIT bit 1 flipped
(entry req_in = 1,0,0, q = 0, rst = 0). `j3_gate` (CellBindKOps) proved by the same
`decide +kernel` must fail: the binding of 3-input compute units sees the netlist. -/
open Formal.Net Formal.Gen Formal.Net.Ops.Gen Formal.Net.CellBind
def mutJ3 : Netlist :=
  { KNets.bd_join_N3 with cells := KNets.bd_join_N3.cells.map (fun c => { c with init := c.init ^^^ 2 }) }
def mj3F (p : Bool × Bool × Bool) (q : Bool) : Bool :=
  genF mutJ3 "u.genblk1.genblk1.g3.u.u" .O
    ["req_in[0]", "req_in[1]", "req_in[2]", "req", "rst"] [p.1, p.2.1, p.2.2, q, false]
theorem mj3_gate : ∀ (p : Bool × Bool × Bool) q, mj3F p q = cel3 p.1 p.2.1 p.2.2 q := by
  intro ⟨a, b, c⟩ q; revert a b c q; decide +kernel
