import Formal.Net.Compute.Ripple
import Formal.Net.Compute.Slt
import Formal.Gen.Compute.GcdD.Uselect1

/-!
# H_COMPUTE_FN for gcd_hw's absolute difference `uselect1`

Problem statement. This `bdc_fused_*` unit (bdc Verilog `d = e0 - e1; z = (d > -1) ? d : 0 - d`,
signed, 32 bits; the gcd loop's `|a - b|`, and the unit where the gcd_rig GLS located the board
failure), as yosys synthesized it (18 CARRY4, 121 cells), computes
`Ops.select (Ops.cmpi .sgt 32 d 0xFFFFFFFF) d (Ops.subi 32 0 d)` with `d = Ops.subi 32 a b`, for
EVERY `a, b` (`uselect1_fn`). This is the FUNCTION; the board failure was a timing/GLS event, which
this theorem does not address (it rules out a wrong synthesized function as its cause).

Proof: the difference chain and the negation chain are `RipOK` ripple chains (`a + ~b + 1`;
`~d + 1` with the 32 difference nets as cut points), the sign test (`d > -1`, which yosys builds as
a constant compare) is checked over its group nets and `d[31]` as cut points, and each output bit
is checked as a mux of `d[i]` and `(-d)[i]` by the sign test.

Assumed / not covered: LUT, CARRY4, INV Boolean semantics (shard A's models); that this is the
placed netlist (11f/11g); timing (the board failure); glitches.
-/

namespace Formal.Net.Compute.GcdD
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.GcdD

def dN : List Nat := [104, 103, 106, 107, 108, 109, 111, 110, 113, 114, 115, 116, 118, 117, 120, 121, 122, 123, 125, 124, 127, 128, 129, 130, 132, 131, 134, 135, 136, 137, 139, 138]
def nN : List Nat := [173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]

def subRip : Rip := ⟨dN, [241, 245, 249, 253, 257, 261, 265], fun i => .inp 0 i, some (fun i => .inp 1 i), false, true, true, []⟩
def negRip : Rip := ⟨nN, [273, 277, 281, 285, 289, 293, 297], fun i => .cut (dN.getD i 0), none, true, false, true, dN⟩

abbrev subBit (i : Nat) : Prop :=
  NetOK Uselect1.cells (subRip.cutset (i / 4)) (subRip.outs.getD i 0) (subRip.leaves (i / 4))
    (fun l => (subRip.sum (i / 4) l).testBit (i % 4))
abbrev subCar (j : Nat) : Prop :=
  NetOK Uselect1.cells (subRip.cutset j) (subRip.cuts.getD j 0) (subRip.leaves j) (fun l => decide (16 ≤ subRip.sum j l))

set_option maxRecDepth 100000 in
theorem sub_b0 : subBit 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b1 : subBit 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b2 : subBit 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b3 : subBit 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b4 : subBit 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b5 : subBit 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b6 : subBit 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b7 : subBit 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b8 : subBit 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b9 : subBit 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b10 : subBit 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b11 : subBit 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b12 : subBit 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b13 : subBit 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b14 : subBit 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b15 : subBit 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b16 : subBit 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b17 : subBit 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b18 : subBit 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b19 : subBit 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b20 : subBit 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b21 : subBit 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b22 : subBit 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b23 : subBit 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b24 : subBit 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b25 : subBit 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b26 : subBit 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b27 : subBit 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b28 : subBit 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b29 : subBit 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b30 : subBit 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_b31 : subBit 31 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_c0 : subCar 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_c1 : subCar 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_c2 : subCar 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_c3 : subCar 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_c4 : subCar 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_c5 : subCar 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sub_c6 : subCar 6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem sub_ok : RipOK Uselect1.cells subRip := by
  refine ⟨rfl, Uselect1.nodup, fun i hi => ?_, fun j hj => ?_⟩
  · match i, hi with
    | 0, _ => exact sub_b0
    | 1, _ => exact sub_b1
    | 2, _ => exact sub_b2
    | 3, _ => exact sub_b3
    | 4, _ => exact sub_b4
    | 5, _ => exact sub_b5
    | 6, _ => exact sub_b6
    | 7, _ => exact sub_b7
    | 8, _ => exact sub_b8
    | 9, _ => exact sub_b9
    | 10, _ => exact sub_b10
    | 11, _ => exact sub_b11
    | 12, _ => exact sub_b12
    | 13, _ => exact sub_b13
    | 14, _ => exact sub_b14
    | 15, _ => exact sub_b15
    | 16, _ => exact sub_b16
    | 17, _ => exact sub_b17
    | 18, _ => exact sub_b18
    | 19, _ => exact sub_b19
    | 20, _ => exact sub_b20
    | 21, _ => exact sub_b21
    | 22, _ => exact sub_b22
    | 23, _ => exact sub_b23
    | 24, _ => exact sub_b24
    | 25, _ => exact sub_b25
    | 26, _ => exact sub_b26
    | 27, _ => exact sub_b27
    | 28, _ => exact sub_b28
    | 29, _ => exact sub_b29
    | 30, _ => exact sub_b30
    | 31, _ => exact sub_b31
    | _ + 32, h => exact absurd h (by omega)
  · match j, hj with
    | 0, _ => exact sub_c0
    | 1, _ => exact sub_c1
    | 2, _ => exact sub_c2
    | 3, _ => exact sub_c3
    | 4, _ => exact sub_c4
    | 5, _ => exact sub_c5
    | 6, _ => exact sub_c6
    | _ + 7, h => exact absurd h (by omega)

abbrev negBit (i : Nat) : Prop :=
  NetOK Uselect1.cells (negRip.cutset (i / 4)) (negRip.outs.getD i 0) (negRip.leaves (i / 4))
    (fun l => (negRip.sum (i / 4) l).testBit (i % 4))
abbrev negCar (j : Nat) : Prop :=
  NetOK Uselect1.cells (negRip.cutset j) (negRip.cuts.getD j 0) (negRip.leaves j) (fun l => decide (16 ≤ negRip.sum j l))

set_option maxRecDepth 100000 in
theorem neg_b0 : negBit 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b1 : negBit 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b2 : negBit 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b3 : negBit 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b4 : negBit 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b5 : negBit 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b6 : negBit 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b7 : negBit 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b8 : negBit 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b9 : negBit 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b10 : negBit 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b11 : negBit 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b12 : negBit 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b13 : negBit 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b14 : negBit 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b15 : negBit 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b16 : negBit 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b17 : negBit 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b18 : negBit 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b19 : negBit 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b20 : negBit 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b21 : negBit 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b22 : negBit 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b23 : negBit 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b24 : negBit 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b25 : negBit 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b26 : negBit 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b27 : negBit 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b28 : negBit 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b29 : negBit 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b30 : negBit 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_b31 : negBit 31 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_c0 : negCar 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_c1 : negCar 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_c2 : negCar 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_c3 : negCar 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_c4 : negCar 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_c5 : negCar 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem neg_c6 : negCar 6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem neg_ok : RipOK Uselect1.cells negRip := by
  refine ⟨rfl, Uselect1.nodup, fun i hi => ?_, fun j hj => ?_⟩
  · match i, hi with
    | 0, _ => exact neg_b0
    | 1, _ => exact neg_b1
    | 2, _ => exact neg_b2
    | 3, _ => exact neg_b3
    | 4, _ => exact neg_b4
    | 5, _ => exact neg_b5
    | 6, _ => exact neg_b6
    | 7, _ => exact neg_b7
    | 8, _ => exact neg_b8
    | 9, _ => exact neg_b9
    | 10, _ => exact neg_b10
    | 11, _ => exact neg_b11
    | 12, _ => exact neg_b12
    | 13, _ => exact neg_b13
    | 14, _ => exact neg_b14
    | 15, _ => exact neg_b15
    | 16, _ => exact neg_b16
    | 17, _ => exact neg_b17
    | 18, _ => exact neg_b18
    | 19, _ => exact neg_b19
    | 20, _ => exact neg_b20
    | 21, _ => exact neg_b21
    | 22, _ => exact neg_b22
    | 23, _ => exact neg_b23
    | 24, _ => exact neg_b24
    | 25, _ => exact neg_b25
    | 26, _ => exact neg_b26
    | 27, _ => exact neg_b27
    | 28, _ => exact neg_b28
    | 29, _ => exact neg_b29
    | 30, _ => exact neg_b30
    | 31, _ => exact neg_b31
    | _ + 32, h => exact absurd h (by omega)
  · match j, hj with
    | 0, _ => exact neg_c0
    | 1, _ => exact neg_c1
    | 2, _ => exact neg_c2
    | 3, _ => exact neg_c3
    | 4, _ => exact neg_c4
    | 5, _ => exact neg_c5
    | 6, _ => exact neg_c6
    | _ + 7, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem cmp_ok : NetOK Uselect1.cells [105, 112, 119, 126, 133, 140, 138] 174
    [.cut 105, .cut 112, .cut 119, .cut 126, .cut 133, .cut 140, .cut 138]
    (fun l => !(l.getD 5 false) && !(l.getD 6 false)) := by decide +kernel

set_option maxRecDepth 100000 in
theorem and140_ok : NetOK Uselect1.cells [134, 135, 136, 137, 138, 139] 140
    [.cut 134, .cut 135, .cut 136, .cut 137, .cut 138, .cut 139] (fun l => l.all id) := by
  decide +kernel

abbrev MuxBit (i : Nat) : Prop :=
  Uselect1.outs.getD i .c0 = .net (outNet Uselect1.outs i) ∧
  NetOK Uselect1.cells [174, dN.getD i 0, nN.getD i 0] (outNet Uselect1.outs i)
    [.cut 174, .cut (dN.getD i 0), .cut (nN.getD i 0)]
    (fun l => if l.getD 0 false then l.getD 1 false else l.getD 2 false)

set_option maxRecDepth 100000 in
theorem mux_ok : ∀ i, i < 32 → MuxBit i := by decide +kernel


end Formal.Net.Compute.GcdD
