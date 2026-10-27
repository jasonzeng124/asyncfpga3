import Formal.Gen.Cells

/-!
# 11d: the non-LUT primitive models, checked against yosys's own mapping

`formal/tools/gen/test/prims.v` (NOT library cells) holds small modules whose
synthesis uses CARRY4, MUXF7, MUXF8, FDRE/FDSE/FDCE/FDPE and LDCE (with
`IS_G_INVERTED`). Each theorem says the interpreter's model of the primitive,
run on the netlist yosys produced from a known Verilog function, computes that
function. This tests the primitive models (and the generator's pin
bit-blasting and inversion handling) against an independent reference: the
Verilog semantics of `+`, `d[sel]`, `always @(posedge c)` and a latch.

What it does NOT test: that yosys's techmapping matches silicon (that is
yosys's and the fabric's business), nor any timing.
-/

namespace Formal.Gen.ProofsPrims
open Formal.Cells Formal.Gen Formal.Gen.Cells

/-- CARRY4 (two of them, the second only for the carry out): `s = a + b + ci`,
all 512 inputs. -/
theorem prims_add_spec : ∀ a, a < 16 → ∀ b, b < 16 → ∀ ci : Bool,
    prims_add.outs boolSem (bitsOf 4 a ++ bitsOf 4 b ++ [ci]) [] =
      some (bitsOf 5 (a + b + ci.toNat)) := by decide +kernel

/-- MUXF7 over two LUT6 4:1 muxes: `z = d[sel]`, all 2048 inputs. -/
theorem prims_mux8_spec : ∀ d, d < 256 → ∀ sel, sel < 8 →
    prims_mux8.outs boolSem (bitsOf 8 d ++ bitsOf 3 sel) [] = some [d.testBit sel] := by
  decide +kernel

/-- MUXF8 over two MUXF7: `z = d[sel]`. -/
theorem prims_muxf8_spec : ∀ d, d < 16 → ∀ sel, sel < 4 →
    prims_muxf8.outs boolSem (bitsOf 4 d ++ bitsOf 2 sel) [] = some [d.testBit sel] := by
  decide +kernel

/-- The Kleene reading of a MUXF7/MUXF8 is `K3.mux` (H_KLEENE_LUT's mux). -/
theorem prims_muxf_kleene : ∀ a b s : K3,
    prims_muxf8.gateN kleeneSem "u0" .O [("l[0]", a), ("l[1]", b), ("sel[0]", s)] = some (K3.mux s a b) ∧
    prims_muxf8.gateN kleeneSem "u2" .O [("m0", a), ("m1", b), ("sel[1]", s)] = some (K3.mux s a b) := by
  decide +kernel

theorem prims_ff_iface :
    prims_ff.inputNames = ["c", "ce", "r", "d"] ∧
    prims_ff.stateNames = ["qr", "qs", "qc", "qp", "qp$master", "qc$master", "qs$master", "qr$master"] ∧
    prims_ff.cellNames.length = 4 := by decide +kernel

theorem ffq_sync : ∀ c ce x d q m : Bool, lutB FFQ_SYNC [c, ce, x, d, q, m] = (if c then m else q) := by
  decide
theorem fdre_m : ∀ c ce d r q m : Bool,
    lutB FDRE_M [c, ce, d, r, q, m] = (if c then m else if r then false else if ce then d else q) := by
  decide
theorem fdse_m : ∀ c ce d s q m : Bool,
    lutB FDSE_M [c, ce, d, s, q, m] = (if c then m else if s then true else if ce then d else q) := by
  decide
theorem fdce_q : ∀ c ce clr d q m : Bool,
    lutB FDCE_Q [c, ce, clr, d, q, m] = (if clr then false else if c then m else q) := by decide
theorem fdce_m : ∀ c ce clr d q m : Bool,
    lutB FDCE_M [c, ce, clr, d, q, m] = (if clr then false else if c then m else if ce then d else q) := by
  decide
theorem fdpe_q : ∀ c ce pre d q m : Bool,
    lutB FDPE_Q [c, ce, pre, d, q, m] = (if pre then true else if c then m else q) := by decide
theorem fdpe_m : ∀ c ce pre d q m : Bool,
    lutB FDPE_M [c, ce, pre, d, q, m] = (if pre then true else if c then m else if ce then d else q) := by
  decide

/-- The four flip-flops, one unit step (H_FF_MS: master-slave), by symbolic
evaluation of the interpreter plus the per-primitive tables above. -/
theorem prims_ff_next (c ce r d qr qs qc qp mp mc ms mr : Bool) :
    prims_ff.next boolSem [c, ce, r, d] [qr, qs, qc, qp, mp, mc, ms, mr] =
      some [if c then mr else qr, if c then ms else qs,
            if r then false else if c then mc else qc, if r then true else if c then mp else qp,
            if r then true else if c then mp else if ce then d else qp,
            if r then false else if c then mc else if ce then d else qc,
            if c then ms else if r then true else if ce then d else qs,
            if c then mr else if r then false else if ce then d else qr] := by
  have h : prims_ff.next boolSem [c, ce, r, d] [qr, qs, qc, qp, mp, mc, ms, mr] =
      some [lutB FFQ_SYNC [c, ce, d, r, qr, mr], lutB FFQ_SYNC [c, ce, d, r, qs, ms],
            lutB FDCE_Q [c, ce, r, d, qc, mc], lutB FDPE_Q [c, ce, r, d, qp, mp],
            lutB FDPE_M [c, ce, r, d, qp, mp], lutB FDCE_M [c, ce, r, d, qc, mc],
            lutB FDSE_M [c, ce, d, r, qs, ms], lutB FDRE_M [c, ce, d, r, qr, mr]] := rfl
  rw [h, ffq_sync, ffq_sync, fdce_q, fdpe_q, fdpe_m, fdce_m, fdse_m, fdre_m]

/-- **Edge semantics.** Clock low for one step, then high: from ANY state,
every flop now holds what its Verilog `always @(posedge c)` block assigns
(`r` sync reset for FDRE/FDSE, async for FDCE/FDPE; `ce` enable). -/
theorem prims_ff_edge (ce r d qr qs qc qp mp mc ms mr : Bool) :
    ((prims_ff.next boolSem [false, ce, r, d] [qr, qs, qc, qp, mp, mc, ms, mr]).bind
      (prims_ff.next boolSem [true, ce, r, d])).map (·.take 4) =
      some [if r then false else if ce then d else qr, if r then true else if ce then d else qs,
            if r then false else if ce then d else qc, if r then true else if ce then d else qp] := by
  rw [prims_ff_next]
  simp only [Option.bind_some, Bool.false_eq_true, ite_false]
  rw [prims_ff_next]
  cases r <;> simp

/-- LDCE with `IS_G_INVERTED = 1` behind a LUT2 NOR (what yosys made of a
latch with reset): `q = r ? 0/1 : (g ? d : q)`. -/
theorem prims_lat_next : ∀ g r d qc qp : Bool,
    prims_lat.inputNames = ["g", "r", "d"] ∧ prims_lat.stateNames = ["qc", "qp"] ∧
    prims_lat.next boolSem [g, r, d] [qc, qp] =
      some [if r then false else if g then d else qc, if r then true else if g then d else qp] := by
  decide +kernel

end Formal.Gen.ProofsPrims
