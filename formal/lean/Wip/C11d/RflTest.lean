import Formal.Gen.Cells
import Formal.Cells.LibCtlMergeMux
open Formal.Cells Formal.Gen Formal.Gen.Cells
open Formal.Cells.LibCtlMergeMux (c2B j0B j1B or2B)

set_option maxHeartbeats 1000000 in
theorem t1 : ∀ rst xr x0 x1 yr y0 y1 cr s za xa ya j0 j1 : Bool,
    bd_mux_W2.next boolSem [rst, xr, x0, x1, yr, y0, y1, cr, s, za] [xa, ya, j0, j1] =
      some [c2B j0 za xa rst, c2B j1 za ya rst, j0B xr cr s j0 rst, j1B yr cr s j1 rst] := by
  intros; rfl

set_option maxHeartbeats 1000000 in
theorem t2 : ∀ rst xr x0 x1 yr y0 y1 cr s za xa ya j0 j1 : Bool,
    bd_mux_W2.outs boolSem [rst, xr, x0, x1, yr, y0, y1, cr, s, za] [xa, ya, j0, j1] =
      some [xa, ya, za, lutB 0x1FF0 [j0, j1] , o5B 0xFFAA5500E4E4E4E4 [s, x0, y0, x1, y1, true],
            o6B 0xFFAA5500E4E4E4E4 [s, x0, y0, x1, y1, true]] := by
  intros; rfl
