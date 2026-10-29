import Formal.Cells.Necessity6Mux
import Formal.Cells.Necessity6MuxN
import Formal.Cells.Necessity6MuxJ
import Formal.Cells.Necessity6PipeSel
/-! P10c item 7: Necessity6* (84bc9e4). -/
#print axioms Formal.Cells.Necessity6Mux.claimY1_false
#print axioms Formal.Cells.Necessity6Mux.claimY0
#print axioms Formal.Cells.Necessity6Mux.N6.passY9
#print axioms Formal.Cells.Necessity6Mux.N6.failY10

namespace P10c7
open Formal.Cells Formal.Cells.OpsTimed Formal.Cells.Necessity4Mux Formal.Cells.Necessity6Mux
/-- ClaimY 0 IS the shipped theorem (mux_ok_staticN at slack 0). -/
example : ClaimY 0 := fun P Wzc Ex Ey Ec Es lj wc wo R rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1
    e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak yak G V Cs S hR => mux_ok_staticN G V Cs S hR
/-- The counter-run violates the SHIPPED premise (slack 0): it is a boundary point, not a
refutation of mux_ok_staticN. -/
example : ¬ MuxStaticN (N6.run 10) uW 1 1 6 1 1 1 1 0 0 := by
  intro h; have := h.S_J1_YR; revert this; decide
/-- and the shipped premise holds at 9 ticks (passY9's run). -/
example : MuxStaticN (N6.run 9) uW 1 1 6 1 1 1 1 0 0 := N6.staticN 9 0 (by omega) (by omega)
end P10c7
