import Formal.Gen.Cells
import Formal.Cells.CElemFn
import Formal.Cells.Latch
import Formal.Cells.LinkHandshake
import Formal.Cells.Bundling

/-!
# 11d: generated links and pipes (`bd_link.v`)

B's transcriptions matched (`Formal.Cells.LinkHandshake`): `INIT_C2N`, `ctlB`
(the Muller controller), `INIT_LAT`/`INIT_PAIR` (latch), `INIT_DB`, `INIT_DA`,
`INIT_DLD`, `INIT_DLT` and **`dNext`** (the decoupled controller, both
`BROAD` values), and **`diNext`** (B's N-stage pipe interleaving model,
N = 2): the generated gates ARE the gates of B's finite-state models, so B's
`dctl_ok1`/`dctl_ok0` (hazard- and deadlock-freedom under H_LT_FIRST) and the
pipe theorems are statements about these synthesized netlists.

Delay lines (`DELAY`, `DACK`, `SDELAY`, `LDN`) are wires in the unit-step
reading; their LUTs are pinned by `_lut` theorems.
-/

namespace Formal.Gen.ProofsLink
open Formal.Cells Formal.Gen Formal.Gen.Cells
open Formal.Cells.Latch (bmux PAIR ODD)
open Formal.Cells.LinkHandshake (INIT_C2N ctlB INIT_DB INIT_DA INIT_DLD INIT_DLT dNext diNext
  INIT_PAIR INIT_LAT pair_eq lat_eq)
open Formal.Cells.Bundling (BUF FF_SIDE FR_SIDE)

/-! ## `bd_link_ctl` -/

theorem bd_link_ctl_lut :
    bd_link_ctl.lutIs "u.u" (.lut 6) INIT_C2N ["req_in", "c_next", "c", "rst", "0", "0"] ["c"] := by
  decide +kernel
theorem bd_link_ctl_gate_B : ∀ r n c rst : Bool,
    bd_link_ctl.gateN boolSem "u.u" .O [("req_in", r), ("c_next", n), ("c", c), ("rst", rst)] =
      some (ctlB r n c rst) := by decide +kernel
theorem bd_link_ctl_gate_K : ∀ r n c rst : K3,
    bd_link_ctl.gateN kleeneSem "u.u" .O [("req_in", r), ("c_next", n), ("c", c), ("rst", rst)] =
      some (Formal.Cells.CElemFn.c2nK r n c rst) := by decide +kernel
theorem bd_link_ctl_next : ∀ r n rst c : Bool,
    bd_link_ctl.inputNames = ["req_in", "c_next", "rst"] ∧
    bd_link_ctl.next boolSem [r, n, rst] [c] = some [ctlB r n c rst] := by decide +kernel

/-! ## `bd_link` (Muller family, the default) -/

theorem link_iface :
    bd_link_W2.inputNames = ["rst", "req_in", "data_in[0]", "data_in[1]", "ack_out"] ∧
    bd_link_W2.outputNames = ["ack_in", "req_out", "data_out[0]", "data_out[1]"] ∧
    bd_link_W2.stateNames = ["ack_in", "data_out[0]", "data_out[1]"] ∧
    bd_link_W2_D2_K2.stateNames = ["data_out[0]", "data_out[1]", "c"] ∧
    bd_link_W2_RF.stateNames = ["ack_in", "data_out[0]", "data_out[1]"] := by decide +kernel

/-- DELAY = DACK = 0: the node `c` IS `req_out` and `ack_in` (bypass lines). -/
theorem bd_link_W2_lut :
    bd_link_W2.cellNames = ["ctl.u.u", "lat.pair[0].u"] ∧
    bd_link_W2.lutIs "ctl.u.u" (.lut 6) INIT_C2N ["req_in", "ack_out", "ack_in", "rst", "0", "0"] ["ack_in"] ∧
    bd_link_W2.lutIs "lat.pair[0].u" .lut6_2 PAIR
      ["data_in[0]", "ack_in", "data_out[0]", "data_in[1]", "data_out[1]", "1"]
      ["data_out[0]", "data_out[1]"] := by decide +kernel

/-- `C = C(req_in, ~ack_out)` with clear; the latch enable is the node. -/
theorem bd_link_W2_step : ∀ rst r d0 d1 ack c q0 q1 : Bool,
    bd_link_W2.next boolSem [rst, r, d0, d1, ack] [c, q0, q1] =
      some [ctlB r ack c rst, bmux c d0 q0, bmux c d1 q1] ∧
    bd_link_W2.outs boolSem [rst, r, d0, d1, ack] [c, q0, q1] = some [c, c, q0, q1] := by
  decide +kernel

/-- DELAY = 2 (symmetric) and DACK = 2 (FASTRISE: buffer then OR with `c`). -/
theorem bd_link_W2_D2_K2_lut :
    bd_link_W2_D2_K2.lutIs "rdly.chain.g[0].u" (.lut 1) BUF ["c"] ["rdly.chain.s[1]"] ∧
    bd_link_W2_D2_K2.lutIs "rdly.chain.g[1].u" (.lut 1) BUF ["rdly.chain.s[1]"] ["req_out"] ∧
    bd_link_W2_D2_K2.lutIs "uack.chain.g[0].u" (.lut 1) BUF ["c"] ["uack.chain.s[1]"] ∧
    bd_link_W2_D2_K2.lutIs "uack.chain.g[1].u" (.lut 2) FR_SIDE ["uack.chain.s[1]", "c"] ["ack_in"] := by
  decide +kernel

theorem bd_link_W2_D2_K2_step : ∀ rst r d0 d1 ack q0 q1 c : Bool,
    bd_link_W2_D2_K2.next boolSem [rst, r, d0, d1, ack] [q0, q1, c] =
      some [bmux c d0 q0, bmux c d1 q1, ctlB r ack c rst] ∧
    bd_link_W2_D2_K2.outs boolSem [rst, r, d0, d1, ack] [q0, q1, c] = some [c, c, q0, q1] := by
  decide +kernel

/-- RFAST = 1: the request line is FASTFALL (AND taps on `c`). -/
theorem bd_link_W2_RF_lut :
    bd_link_W2_RF.lutIs "rdly.chain.g[1].u" (.lut 2) FF_SIDE ["rdly.chain.s[1]", "ack_in"] ["req_out"] := by
  decide +kernel

/-! ## `bd_link_dctl`: the generated gates are B's `dNext` -/

/-- B's variable encoding (`LinkHandshake` Section 6): bit 0 `req_in`, 1 `b`,
2 `a`, 3 `ld`, 4 `lt`, 5 `ack_out`; reset low. -/
def dEnv (s : Nat) : List (String × Bool) :=
  [("req_in", s.testBit 0), ("b", s.testBit 1), ("a", s.testBit 2), ("ld", s.testBit 3),
   ("lt", s.testBit 4), ("ack_out", s.testBit 5), ("rst", false)]

theorem bd_link_dctl_B1_lut :
    bd_link_dctl_B1.lutIs "ub" (.lut 6) INIT_DB ["req_in", "ack_out", "ld", "b", "rst", "0"] ["b"] ∧
    bd_link_dctl_B1.lutIs "ua" (.lut 6) INIT_DA ["req_in", "b", "ld", "a", "rst", "0"] ["a"] ∧
    bd_link_dctl_B1.lutIs "uld" (.lut 6) INIT_DLD ["lt", "1", "a", "ld", "rst", "0"] ["ld"] ∧
    bd_link_dctl_B1.lutIs "ult" (.lut 6) INIT_DLT ["b", "a", "ack_out", "0", "0", "0"] ["lt"] := by
  decide +kernel

/-- **BROAD = 1:** every gate of the synthesized controller, in every one of
B's 64 states, computes B's `dNext true`. -/
theorem bd_link_dctl_B1_dNext : ∀ s, s < 64 →
    bd_link_dctl_B1.gateN boolSem "ub" .O (dEnv s) = some (dNext true s 1) ∧
    bd_link_dctl_B1.gateN boolSem "ua" .O (dEnv s) = some (dNext true s 2) ∧
    bd_link_dctl_B1.gateN boolSem "uld" .O (dEnv s) = some (dNext true s 3) ∧
    bd_link_dctl_B1.gateN boolSem "ult" .O (dEnv s) = some (dNext true s 4) := by decide +kernel

/-- **BROAD = 0** (`gate` tied low): B's `dNext false`. -/
theorem bd_link_dctl_B0_dNext : ∀ s, s < 64 →
    bd_link_dctl_B0.gateN boolSem "ub" .O (dEnv s) = some (dNext false s 1) ∧
    bd_link_dctl_B0.gateN boolSem "ua" .O (dEnv s) = some (dNext false s 2) ∧
    bd_link_dctl_B0.gateN boolSem "uld" .O (dEnv s) = some (dNext false s 3) ∧
    bd_link_dctl_B0.gateN boolSem "ult" .O (dEnv s) = some (dNext false s 4) := by decide +kernel

/-- LDN = 2: `uld` reads `s`, a FASTFALL line on `lt` (B's `dNext` has `s = 1`,
LDN = 0, so this variant is pinned structurally only). -/
theorem bd_link_dctl_B0_L2_lut :
    bd_link_dctl_B0_L2.lutIs "uld" (.lut 6) INIT_DLD ["lt", "s", "a", "ld", "rst", "0"] ["ld"] ∧
    bd_link_dctl_B0_L2.lutIs "withs.us.chain.g[0].u" (.lut 1) BUF ["lt"] ["withs.us.chain.s[1]"] ∧
    bd_link_dctl_B0_L2.lutIs "withs.us.chain.g[1].u" (.lut 2) FF_SIDE ["withs.us.chain.s[1]", "lt"] ["s"] := by
  decide +kernel

/-! ## `bd_link_dc`, and `bd_link` under `-DBD_LINK_DC` -/

theorem dc_iface :
    bd_link_dc_W2.stateNames = ["data_out[0]", "data_out[1]", "b", "ctl.ld", "a"] ∧
    bd_link_W2_DC.stateNames = ["ack_in", "req_out", "data_out[0]", "data_out[1]", "ctl.ld"] := by
  decide +kernel

/-- One step of the decoupled stage with its latch (enable `lt`), the four
LUTs read from B's INIT constants (symbolic evaluation, then B's `pair_eq`). -/
theorem bd_link_W2_DC_step (rst r d0 d1 ack a b q0 q1 ld : Bool) :
    let lt := lutB INIT_DLT [b, a, ack, false, false, false]
    bd_link_W2_DC.next boolSem [rst, r, d0, d1, ack] [a, b, q0, q1, ld] =
      some [lutB INIT_DA [r, b, ld, a, rst, false], lutB INIT_DB [r, ack, ld, b, rst, false],
            bmux lt d0 q0, bmux lt d1 q1, lutB INIT_DLD [lt, true, a, ld, rst, false]] ∧
    bd_link_W2_DC.outs boolSem [rst, r, d0, d1, ack] [a, b, q0, q1, ld] = some [a, b, q0, q1] := by
  intro lt
  refine ⟨?_, rfl⟩
  have h : bd_link_W2_DC.next boolSem [rst, r, d0, d1, ack] [a, b, q0, q1, ld] =
      some [lutB INIT_DA [r, b, ld, a, rst, false], lutB INIT_DB [r, ack, ld, b, rst, false],
            o5B INIT_PAIR [d0, lt, q0, d1, q1, true], o6B INIT_PAIR [d0, lt, q0, d1, q1, true],
            lutB INIT_DLD [lt, true, a, ld, rst, false]] := rfl
  rw [h, (pair_eq _ _ _ _ _).1, (pair_eq _ _ _ _ _).2]; rfl

/-- `bd_link_dc` (DELAY = DACK = 1) is the same netlist plus two buffers. -/
theorem bd_link_dc_W2_step (rst r d0 d1 ack q0 q1 b ld a : Bool) :
    let lt := lutB INIT_DLT [b, a, ack, false, false, false]
    bd_link_dc_W2.next boolSem [rst, r, d0, d1, ack] [q0, q1, b, ld, a] =
      some [bmux lt d0 q0, bmux lt d1 q1, lutB INIT_DB [r, ack, ld, b, rst, false],
            lutB INIT_DLD [lt, true, a, ld, rst, false], lutB INIT_DA [r, b, ld, a, rst, false]] ∧
    bd_link_dc_W2.outs boolSem [rst, r, d0, d1, ack] [q0, q1, b, ld, a] = some [a, b, q0, q1] := by
  intro lt
  have h : bd_link_dc_W2.next boolSem [rst, r, d0, d1, ack] [q0, q1, b, ld, a] =
      some [o5B INIT_PAIR [d0, lt, q0, d1, q1, true], o6B INIT_PAIR [d0, lt, q0, d1, q1, true],
            lutB INIT_DB [r, ack, ld, b, rst, false],
            lutB INIT_DLD [lt, true, a, ld, rst, false], lutB INIT_DA [r, b, ld, a, rst, false]] := rfl
  have ho : bd_link_dc_W2.outs boolSem [rst, r, d0, d1, ack] [q0, q1, b, ld, a] =
      some [lutB BUF [a], lutB BUF [b], q0, q1] := rfl
  rw [h, ho, (pair_eq _ _ _ _ _).1, (pair_eq _ _ _ _ _).2]
  cases a <;> cases b <;> exact ⟨rfl, rfl⟩

/-! ## `bd_pipe` -/

theorem pipe_iface :
    bd_pipe_W1_N2.inputNames = ["rst", "req_in", "data_in", "ack_out"] ∧
    bd_pipe_W1_N2.stateNames = ["ack_in", "req_out", "data_out", "many.dat[1]"] ∧
    bd_pipe_W1_N1.stateNames = ["ack_in", "data_out"] := by decide +kernel

theorem bd_pipe_W1_N1_step : ∀ rst r d ack c q : Bool,
    bd_pipe_W1_N1.next boolSem [rst, r, d, ack] [c, q] = some [ctlB r ack c rst, bmux c d q] := by
  decide +kernel

/-- N = 2: stage 1's request is stage 0's node through the SDELAY = 1 line. -/
theorem bd_pipe_W1_N2_step : ∀ rst r d ack c0 c1 q1 q0 : Bool,
    bd_pipe_W1_N2.next boolSem [rst, r, d, ack] [c0, c1, q1, q0] =
      some [ctlB r c1 c0 rst, ctlB c0 ack c1 rst, bmux c1 q0 q1, bmux c0 d q0] ∧
    bd_pipe_W1_N2.lutIs "many.stage[0].u.rdly.chain.g[0].u" (.lut 1) BUF ["ack_in"] ["many.r[1]"] := by
  decide +kernel

/-- B's interleaving model of the 2-stage pipe (`diNext 2`, vars: 0 `req_in`,
2/5 nodes `c_0`/`c_1`, 3/6 their forward copies `f_i`, 4/7 backward copies
`b_i`, 8 `a`, 9 `aw`): in every one of its 1024 states, the two controller
gates of the synthesized pipe compute B's next value, with each net read from
the copy B's model gives that gate (forward copy at the next stage's I0,
backward copy at the previous stage's I1, the node itself at its feedback pin). -/
theorem bd_pipe_W1_N2_diNext : ∀ s, s < 1024 →
    bd_pipe_W1_N2.gateN boolSem "many.stage[0].u.ctl.u.u" .O
      [("req_in", s.testBit 1), ("req_out", s.testBit 7), ("ack_in", s.testBit 2), ("rst", false)] =
      some (diNext 2 s 2) ∧
    bd_pipe_W1_N2.gateN boolSem "many.stage[1].u.ctl.u.u" .O
      [("many.r[1]", s.testBit 3), ("ack_out", s.testBit 9), ("req_out", s.testBit 5), ("rst", false)] =
      some (diNext 2 s 5) := by decide +kernel

/-- Decoupled pipe, N = 2 (internal boundary BROAD = 0, last stage BROAD = 1;
stage 1's request is stage 0's `b` through the SDELAY = 1 buffer). Symbolic
evaluation, then B's `lat_eq` for the two odd latch bits. -/
theorem bd_pipe_dc_W1_N2_step (rst r d ack a0 b1 q1 b0 ld0 a1 q0 ld1 : Bool) :
    let lt0 := lutB INIT_DLT [b0, a0, false, false, false, false]
    let lt1 := lutB INIT_DLT [b1, a1, ack, false, false, false]
    let r1 := lutB BUF [b0]
    bd_pipe_dc_W1_N2.next boolSem [rst, r, d, ack] [a0, b1, q1, b0, ld0, a1, q0, ld1] =
      some [lutB INIT_DA [r, b0, ld0, a0, rst, false], lutB INIT_DB [r1, ack, ld1, b1, rst, false],
            bmux lt1 q0 q1, lutB INIT_DB [r, a1, ld0, b0, rst, false],
            lutB INIT_DLD [lt0, true, a0, ld0, rst, false], lutB INIT_DA [r1, b1, ld1, a1, rst, false],
            bmux lt0 d q0, lutB INIT_DLD [lt1, true, a1, ld1, rst, false]] := by
  intro lt0 lt1 r1
  have h : bd_pipe_dc_W1_N2.next boolSem [rst, r, d, ack] [a0, b1, q1, b0, ld0, a1, q0, ld1] =
      some [lutB INIT_DA [r, b0, ld0, a0, rst, false], lutB INIT_DB [r1, ack, ld1, b1, rst, false],
            lutB INIT_LAT [q0, lt1, q1, false, false, false], lutB INIT_DB [r, a1, ld0, b0, rst, false],
            lutB INIT_DLD [lt0, true, a0, ld0, rst, false], lutB INIT_DA [r1, b1, ld1, a1, rst, false],
            lutB INIT_LAT [d, lt0, q0, false, false, false], lutB INIT_DLD [lt1, true, a1, ld1, rst, false]] :=
    rfl
  rw [h, lat_eq, lat_eq]; rfl

/-- The SDELAY buffer is a wire in steady state. -/
theorem buf_id : ∀ b : Bool, lutB BUF [b] = b := by decide

end Formal.Gen.ProofsLink
