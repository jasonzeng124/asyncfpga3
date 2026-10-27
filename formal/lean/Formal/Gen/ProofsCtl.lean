import Formal.Gen.Cells
import Formal.Gen.PrelimSem
import Formal.Cells.LibCtlMergeMux
import Formal.Core.Lut
import Formal.Core.LutCells

/-!
# 11d: generated steer, protocol converters, merge and mux (`bd_ctl.v`, `bd_merge.v`, `bd_mux.v`)

B's transcriptions matched (all in `Formal.Cells.LibCtlMergeMux`):
`INIT_steer`, `req0B/K`, `req1B/K`, `INIT_or2`, `or2B/K` (steer, `bd_bd2dr`,
`bd_dr2bd` bare); `INIT_dr`, `dNextB/K`, `eitherB/K` (`bd_dr2bd` HOLD=1),
`dBare` (HOLD=0); `INIT_c2`, `c2B/K`, `selB/K` (merge); `INIT_j0`, `INIT_j1`,
`j0B/K`, `j1B/K` (mux). Forms as in `ProofsCE`.
-/

namespace Formal.Gen.ProofsCtl
set_option linter.constructorNameAsVariable false
open Formal.Cells Formal.Gen Formal.Gen.Cells
open Formal.Cells.LibCtlMergeMux (INIT_steer INIT_or2 req0B req1B req0K req1K or2B or2K
  INIT_dr dNextB dNextK eitherB eitherK dBare INIT_c2 c2B c2K selB selK INIT_j0 INIT_j1
  j0B j1B j0K j1K)

/-! ## `bd_steer` -/

theorem bd_steer_lut :
    bd_steer.lutIs "u" .lut6_2 INIT_steer ["req", "s", "0", "0", "0", "1"] ["req0", "req1"] ∧
    bd_steer.lutIs "uack" (.lut 2) INIT_or2 ["ack0", "ack1"] ["ack"] := by decide +kernel

theorem bd_steer_gate_K : ∀ req s a0 a1 : K3,
    bd_steer.gateN kleeneSemP "u" .O5 [("req", req), ("s", s)] = some (req0K req s) ∧
    bd_steer.gateN kleeneSemP "u" .O6 [("req", req), ("s", s)] = some (req1K req s) ∧
    bd_steer.gateN kleeneSemP "uack" .O [("ack0", a0), ("ack1", a1)] = some (or2K a0 a1) := by
  decide +kernel

theorem bd_steer_gate_B : ∀ req s a0 a1 : Bool,
    bd_steer.gateN boolSem "u" .O5 [("req", req), ("s", s)] = some (req0B req s) ∧
    bd_steer.gateN boolSem "u" .O6 [("req", req), ("s", s)] = some (req1B req s) ∧
    bd_steer.gateN boolSem "uack" .O [("ack0", a0), ("ack1", a1)] = some (or2B a0 a1) := by
  decide +kernel

/-- Header equations: `req0 = req.~s`, `req1 = req.s`, `ack = ack0 + ack1`. -/
theorem bd_steer_outs : ∀ req s a0 a1 : Bool,
    bd_steer.inputNames = ["req", "s", "ack0", "ack1"] ∧
    bd_steer.outputNames = ["ack", "req0", "req1"] ∧
    bd_steer.outs boolSem [req, s, a0, a1] [] = some [a0 || a1, req && !s, req && s] := by
  decide +kernel

/-! ## `bd_bd2dr`, `bd_dr2bd` -/

/-- The same LUT as the steer, `f` on O5 and `t` on O6 (header: "pin for pin
the same circuit"). -/
theorem bd_bd2dr_lut :
    bd_bd2dr.lutIs "u" .lut6_2 INIT_steer ["req", "d", "0", "0", "0", "1"] ["f", "t"] := by
  decide +kernel

theorem bd_bd2dr_outs : ∀ req d ackdr : Bool,
    bd_bd2dr.inputNames = ["req", "d", "ack_dr"] ∧
    bd_bd2dr.outputNames = ["ack", "t", "f"] ∧
    bd_bd2dr.outs boolSem [req, d, ackdr] [] = some [ackdr, req1B req d, req0B req d] ∧
    bd_bd2dr.outs boolSem [req, d, ackdr] [] = some [ackdr, req && d, req && !d] := by
  decide +kernel

theorem bd_dr2bd_D2_lut :
    bd_dr2bd_D2.lutIs "gbare.uor" (.lut 2) INIT_or2 ["t", "f"] ["either"] := by decide +kernel

/-- HOLD = 0: `d = t` (B's `dBare`), `req` = the OR through the line. -/
theorem bd_dr2bd_D2_outs : ∀ t f ack : Bool,
    bd_dr2bd_D2.inputNames = ["t", "f", "ack"] ∧
    bd_dr2bd_D2.outputNames = ["ack_dr", "req", "d"] ∧
    bd_dr2bd_D2.outs boolSem [t, f, ack] [] = some [ack, or2B t f, dBare t f false] := by
  decide +kernel

theorem bd_dr2bd_D2_H_lut :
    bd_dr2bd_D2_H.lutIs "ghold.u" .lut6_2 INIT_dr ["t", "f", "d", "0", "0", "1"] ["d", "either"] := by
  decide +kernel

theorem bd_dr2bd_D2_H_gate_K : ∀ t f d : K3,
    bd_dr2bd_D2_H.gateN kleeneSemP "ghold.u" .O5 [("t", t), ("f", f), ("d", d)] = some (dNextK t f d) ∧
    bd_dr2bd_D2_H.gateN kleeneSemP "ghold.u" .O6 [("t", t), ("f", f), ("d", d)] = some (eitherK t f d) := by
  decide +kernel

/-- HOLD = 1, unit step, state `[d]`: `d' = C(t, ~f)` (B's `dNextB`), `req = t + f`. -/
theorem bd_dr2bd_D2_H_step : ∀ t f ack d : Bool,
    bd_dr2bd_D2_H.stateNames = ["d"] ∧
    bd_dr2bd_D2_H.next boolSem [t, f, ack] [d] = some [dNextB t f d] ∧
    bd_dr2bd_D2_H.outs boolSem [t, f, ack] [d] = some [ack, eitherB t f d, d] := by
  decide +kernel

theorem ctl_inits_core :
    bd_steer.initOf "u" = some Formal.Core.LutCells.bd_steer_u.init := by decide +kernel

/-! ## `bd_merge` (W = 2, DELAY = 2) -/

theorem bd_merge_W2_lut :
    bd_merge_W2.lutIs "uor" (.lut 2) INIT_or2 ["x_req", "y_req"] ["either"] ∧
    bd_merge_W2.lutIs "usel" (.lut 2) INIT_or2 ["x_req", "x_ack"] ["sel"] ∧
    bd_merge_W2.lutIs "uxa.u" (.lut 6) INIT_c2 ["x_req", "z_ack", "x_ack", "rst", "0", "0"] ["x_ack"] ∧
    bd_merge_W2.lutIs "uya.u" (.lut 6) INIT_c2 ["y_req", "z_ack", "y_ack", "rst", "0", "0"] ["y_ack"] ∧
    bd_merge_W2.lutIs "udat.pair[0].u" .lut6_2 Formal.Core.Init.datamux_pair.init.toNat
      ["sel", "y_data[0]", "x_data[0]", "y_data[1]", "x_data[1]", "1"] ["z_data[0]", "z_data[1]"] := by
  decide +kernel

theorem bd_merge_W2_gate_K : ∀ xr za xa xq : K3,
    bd_merge_W2.gateN kleeneSemP "uxa.u" .O [("x_req", xr), ("z_ack", za), ("x_ack", xq), ("rst", .f)] =
      some (c2K xr za xq .f) ∧
    bd_merge_W2.gateN kleeneSemP "usel" .O [("x_req", xr), ("x_ack", xa)] = some (selK xr xa) := by
  decide +kernel

/-- Two buffers after an OR (the `DELAY = 2` request line): steady state is the OR. -/
theorem buf2_or : ∀ a b : Bool, lutB 0x2 [lutB 0x2 [lutB INIT_or2 [a, b]]] = or2B a b := by decide
/-- The datamux pair (`Init.datamux_pair`), both outputs. -/
theorem dmux_pair : ∀ s a0 b0 a1 b1 : Bool,
    o5B 0xFFAA5500E4E4E4E4 [s, a0, b0, a1, b1, true] = (if s then b0 else a0) ∧
    o6B 0xFFAA5500E4E4E4E4 [s, a0, b0, a1, b1, true] = (if s then b1 else a1) := by decide

/-- Merge, unit step (state `[x_ack, y_ack]`): the two acknowledge C-elements
(B's `c2B`), `z_req = x_req + y_req` through the line, `z_data = sel ? x : y`
with `sel = x_req + x_ack` (B's `selB`). Proved by symbolic evaluation (`rfl`:
the interpreter on the generated data reduces to these LUT terms) plus the
small exhaustive lemmas above. -/
theorem bd_merge_W2_step (rst xr x0 x1 yr y0 y1 za xa ya : Bool) :
    bd_merge_W2.next boolSem [rst, xr, x0, x1, yr, y0, y1, za] [xa, ya] =
      some [c2B xr za xa rst, c2B yr za ya rst] ∧
    bd_merge_W2.outs boolSem [rst, xr, x0, x1, yr, y0, y1, za] [xa, ya] =
      some [xa, ya, or2B xr yr, if selB xr xa then x0 else y0, if selB xr xa then x1 else y1] := by
  refine ⟨rfl, ?_⟩
  have h : bd_merge_W2.outs boolSem [rst, xr, x0, x1, yr, y0, y1, za] [xa, ya] =
      some [xa, ya, lutB 0x2 [lutB 0x2 [lutB INIT_or2 [xr, yr]]],
            o5B 0xFFAA5500E4E4E4E4 [selB xr xa, y0, x0, y1, x1, true],
            o6B 0xFFAA5500E4E4E4E4 [selB xr xa, y0, x0, y1, x1, true]] := rfl
  rw [h, buf2_or, (dmux_pair _ _ _ _ _).1, (dmux_pair _ _ _ _ _).2]

/-! ## `bd_mux` (W = 2, DELAY = 2, and FASTFALL = 1) -/

theorem bd_mux_W2_lut :
    bd_mux_W2.lutIs "uj0" (.lut 6) INIT_j0 ["x_req", "ctl_req", "s", "j0", "rst", "0"] ["j0"] ∧
    bd_mux_W2.lutIs "uj1" (.lut 6) INIT_j1 ["y_req", "ctl_req", "s", "j1", "rst", "0"] ["j1"] ∧
    bd_mux_W2.lutIs "uor" (.lut 2) INIT_or2 ["j0", "j1"] ["either"] ∧
    bd_mux_W2.lutIs "uxa.u" (.lut 6) INIT_c2 ["j0", "z_ack", "x_ack", "rst", "0", "0"] ["x_ack"] ∧
    bd_mux_W2.lutIs "uya.u" (.lut 6) INIT_c2 ["j1", "z_ack", "y_ack", "rst", "0", "0"] ["y_ack"] ∧
    bd_mux_W2.lutIs "udat.pair[0].u" .lut6_2 Formal.Core.Init.datamux_pair.init.toNat
      ["s", "x_data[0]", "y_data[0]", "x_data[1]", "y_data[1]", "1"] ["z_data[0]", "z_data[1]"] ∧
    bd_mux_W2_FF.lutIs "udly.chain.g[1].u" (.lut 2) 0x8 ["udly.chain.s[1]", "either"] ["z_req"] := by
  decide +kernel

theorem bd_mux_W2_gate_K : ∀ x c s q rst : K3,
    bd_mux_W2.gateN kleeneSemP "uj0" .O [("x_req", x), ("ctl_req", c), ("s", s), ("j0", q), ("rst", rst)] =
      some (j0K x c s q rst) ∧
    bd_mux_W2.gateN kleeneSemP "uj1" .O [("y_req", x), ("ctl_req", c), ("s", s), ("j1", q), ("rst", rst)] =
      some (j1K x c s q rst) := by decide +kernel

/-- Mux, unit step (state `[x_ack, y_ack, j0, j1]`): B's `j0B`/`j1B` joins and
`c2B` acknowledges; `ctl_ack = z_ack`; `z_req = j0 + j1`; `z_data = s ? y : x`.
(2^14 cases: by symbolic evaluation, not enumeration.) -/
theorem bd_mux_W2_step (rst xr x0 x1 yr y0 y1 cr s za xa ya j0 j1 : Bool) :
    bd_mux_W2.next boolSem [rst, xr, x0, x1, yr, y0, y1, cr, s, za] [xa, ya, j0, j1] =
      some [c2B j0 za xa rst, c2B j1 za ya rst, j0B xr cr s j0 rst, j1B yr cr s j1 rst] ∧
    bd_mux_W2.outs boolSem [rst, xr, x0, x1, yr, y0, y1, cr, s, za] [xa, ya, j0, j1] =
      some [xa, ya, za, or2B j0 j1, if s then y0 else x0, if s then y1 else x1] := by
  refine ⟨rfl, ?_⟩
  have h : bd_mux_W2.outs boolSem [rst, xr, x0, x1, yr, y0, y1, cr, s, za] [xa, ya, j0, j1] =
      some [xa, ya, za, lutB 0x2 [lutB 0x2 [lutB INIT_or2 [j0, j1]]],
            o5B 0xFFAA5500E4E4E4E4 [s, x0, y0, x1, y1, true],
            o6B 0xFFAA5500E4E4E4E4 [s, x0, y0, x1, y1, true]] := rfl
  rw [h, buf2_or, (dmux_pair _ _ _ _ _).1, (dmux_pair _ _ _ _ _).2]

end Formal.Gen.ProofsCtl
