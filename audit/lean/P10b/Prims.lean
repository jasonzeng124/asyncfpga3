import Formal.Core.Prims.GenCheck
import Formal.Core.Prims.Hops
import Formal.Core.Prims.SeqXray
import Formal.Core.Prims.SeqSync
import Formal.Core.Prims.DspTimed

/-! Auditor P10b: commits 8cc8788 (Prims comb), 53d5cc9 (Seq), 8c97528 (Dsp). -/

namespace Audit.P10b
open Formal.Core Formal.Core.Prims

/-! ## 1. Axioms of the headline theorems -/
#print axioms Formal.Core.Prims.adder
#print axioms Formal.Core.Prims.kout_sic
#print axioms Formal.Core.Prims.sic_glitch_free
#print axioms Formal.Core.Prims.two_pin_hazard
#print axioms Formal.Core.Prims.co0_glitch
#print axioms Formal.Core.Prims.co0_orders_admissible
#print axioms Formal.Core.Prims.support_matches_xray
#print axioms Formal.Core.Prims.data_first_glitch
#print axioms Formal.Core.Prims.data_first_glitch_xray
#print axioms Formal.Core.Prims.glitch_width_table
#print axioms Formal.Core.Prims.sel_slowest
#print axioms Formal.Core.Prims.GenCheck.carry4_eq
#print axioms Formal.Core.Prims.GenCheck.carry4_c0
#print axioms Formal.Core.Prims.GenCheck.lut62_o6_eq
#print axioms Formal.Core.Prims.GenCheck.lut62_o5_eq
#print axioms Formal.Core.Prims.GenCheck.muxf_eq
#print axioms Formal.Core.Prims.Seq.capture
#print axioms Formal.Core.Prims.Seq.x_contained
#print axioms Formal.Core.Prims.Seq.violation_X
#print axioms Formal.Core.Prims.Seq.sim_rel
#print axioms Formal.Core.Prims.Seq.sync_two_flop
#print axioms Formal.Core.Prims.Seq.regFF_inhabited
#print axioms Formal.Core.Prims.Seq.fast_hold_mismatch
#print axioms Formal.Core.Prims.Dsp.ipowMul_eq
#print axioms Formal.Core.Prims.Dsp.ipow_cells_supported
#print axioms Formal.Core.Prims.DspTimed.ipow_mul_settles
#print axioms Formal.Core.Prims.DspTimed.settle_px
#print axioms Formal.Core.Prims.DspTimed.lumped_tight
#print axioms Formal.Core.Prims.DspTimed.ipow_mul_nonvacuous

/-! ## 2. CARRY4 against my own reading of UG474 (MUXCY: S=1 propagates CI, S=0 takes
DI; XORCY: O = S xor CI), written independently of `bc1..bc4`. -/

/-- My carry chain: carry into stage i (c 0 = CYINIT/CIN). -/
def myC (x : Fin 9 → Bool) : Nat → Bool
  | 0 => x 0
  | i + 1 =>
    if i < 4 then
      (if x ⟨5 + i % 4, by omega⟩ then myC x i else x ⟨1 + i % 4, by omega⟩)
    else false

def myOut (x : Fin 9 → Bool) : COut → Bool
  | .o0 => xor (x 5) (myC x 0) | .o1 => xor (x 6) (myC x 1)
  | .o2 => xor (x 7) (myC x 2) | .o3 => xor (x 8) (myC x 3)
  | .co0 => myC x 1 | .co1 => myC x 2 | .co2 => myC x 3 | .co3 => myC x 4

/-- Their Boolean CARRY4 equals my UG474 reading on all 512 x 8 cases. -/
theorem bout_eq_mine : ∀ (x : Fin 9 → Bool) (o : COut), bout x o = myOut x o := by
  decide +kernel

/-- Adder with the OTHER DI choice (DI = b) also works: semantics, not a coincidence of DI = a. -/
def addVecB (a b : Nat) (ci : Bool) : Fin 9 → Bool := fun i =>
  match i.val with
  | 0 => ci
  | 1 => b.testBit 0 | 2 => b.testBit 1 | 3 => b.testBit 2 | 4 => b.testBit 3
  | 5 => a.testBit 0 ^^ b.testBit 0 | 6 => a.testBit 1 ^^ b.testBit 1
  | 7 => a.testBit 2 ^^ b.testBit 2 | _ => a.testBit 3 ^^ b.testBit 3

theorem adderB : ∀ a, a < 16 → ∀ b, b < 16 → ∀ ci : Bool,
    sumOf (addVecB a b ci) = a + b + ci.toNat := by decide

/-- Mutation: MUXCY polarity swapped (S=1 takes DI) is NOT an adder (adder fails). -/
def mutOut (x : Fin 9 → Bool) : Nat :=
  let c1 := if x 5 then x 1 else x 0
  let c2 := if x 6 then x 2 else c1
  let c3 := if x 7 then x 3 else c2
  let c4 := if x 8 then x 4 else c3
  (xor (x 5) (x 0)).toNat + 2 * (xor (x 6) c1).toNat + 4 * (xor (x 7) c2).toNat +
    8 * (xor (x 8) c3).toNat + 16 * c4.toNat

theorem mutation_detected : mutOut (addVec 1 1 false) ≠ 2 := by decide

/-! ## 3. Spot checks of generated numbers against my own SDF extraction
(the full 506-band comparison is audit/P10b/xcheck.py; these restate a few by rfl). -/
theorem spot1 : selmux .slicel .f7a = ⟨⟨53, 67, 153, 190⟩, ⟨55, 69, 156, 193⟩, ⟨85, 106, 222, 276⟩⟩ := rfl
theorem spot2 : carry4Arc .slicem .o5 .di0 .co3 = some ⟨124, 164, 338, 445⟩ := rfl
theorem spot3 : outMux .slicel .A .lut5 = some ⟨62, 78, 163, 202⟩ := rfl
/-- My min glitch widths: SLICEL F7BMUX fast 93-77 = 16, slow 239-217 = 22. -/
theorem spot4 : (selmux .slicel .f7b).s.lo .fast - (selmux .slicel .f7b).i0.hi .fast = 16 ∧
    (selmux .slicel .f7b).s.lo .slow - (selmux .slicel .f7b).i0.hi .slow = 22 := by decide

/-! ## 4. Seq: windows (SLICEL REG_INIT_FF: SETUP DIN (-0.055::-0.045), HOLD DIN (0.194::0.241)) -/
theorem seq_spot (c : Seq.XCorner) (rv : Bool) (r : Nat) :
    (Seq.regFF c rv r).dLo = 45 ∧ (Seq.regFF c rv r).dHi = 241 ∧
    (Seq.regFF c rv r).ceLo = -109 ∧ (Seq.regFF c rv r).ceHi = -9 := by
  cases c <;> cases rv <;> simp [Seq.regFF, Seq.cs]

/-- The model is SLICEL-only: SLICEM's REG_INIT_FF has HOLD DIN (0.211::0.262) and
SETUP DIN (-0.074::-0.06), i.e. window [60, 262]; `regFF`'s [45, 241] does not contain it
(the end 262 > 241): for a SLICEM flop the SLICEL window is too narrow (unsafe side). -/
theorem slicem_window_not_covered (c : Seq.XCorner) (rv : Bool) (r : Nat) :
    (Seq.regFF c rv r).dHi < 262 := by cases c <;> cases rv <;> simp [Seq.regFF, Seq.cs]

/-- `res` (H_FF_RESOLVE) is a free parameter: the "definite after cqHi+res" bound is a field
of `FlopRel` (`resolve`), assumed for every res, including absurd ones (here 10^12 ps). -/
example (ck : Substrate.Sig) (r ce d : Substrate.KSig) :
    ∃ q, Seq.FlopRel (Seq.regFF .slow false (10 ^ 12)) false false false ck r ce d q :=
  Seq.regFF_inhabited .slow false false false (10 ^ 12) ck r ce d

/-! ## 5. DSP -/
open Formal.Core.Prims.Dsp Formal.Core.Prims.DspTimed in
/-- My recomputation of the critical path: 4036 (A->PCOUT) + 1713 (PCIN->PCOUT) + 1518 (PCIN->P). -/
theorem dsp_crit :
    DspData.pxA_PCOUT.smax + DspData.pxPCIN_PCOUT.smax + DspData.pxPCIN_P.smax = 7267 ∧
    DspData.pxA_PCOUT.fmax + DspData.pxPCIN_PCOUT.fmax + DspData.pxPCIN_P.fmax = 3074 ∧
    settleHi (pxArcs .slow) (0, 0) = 7267 := by decide

open Formal.Core.Prims.Dsp in
/-- Mutation: a middle DSP with Z = PCIN (OPMODE 001 instead of 101, no >>>17) breaks it. -/
def mutMul (a b : Nat) : Nat :=
  headP a b % 2 ^ 17 + 2 ^ 17 *
    (pOut .pcin (hi15 a) (lo17 b) (pOut .pcin (acoutF true 0 (headAc a)) (hi15 b) (headP a b)) % 2 ^ 15)

open Formal.Core.Prims.Dsp in
theorem dsp_mutation_detected : mutMul 131071 131071 ≠ muli32 131071 131071 := by decide

open Formal.Core.Prims.Dsp in
/-- 'for all inputs': operands wider than 32 bits are fine too (only low bits wired). -/
example : ipowMul (2 ^ 40 + 12345) (2 ^ 33 + 777) = muli32 (2 ^ 40 + 12345) (2 ^ 33 + 777) :=
  ipowMul_eq _ _

end Audit.P10b
