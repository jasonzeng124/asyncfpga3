import Formal.Net.Compute.Ripple
import Formal.Net.Compute.Sgt
import Formal.Gen.Compute.Xs.Uaddi0
import Formal.Gen.Compute.Xs.Ucmpi0
import Formal.Gen.Compute.Xs.Ucmpi1
import Formal.Gen.Compute.Xs.Uxori1
import Formal.Gen.Compute.Xs.Uxori2

/-!
# H_COMPUTE_FN on a second kernel: the five compute units of xorshift

Problem statement. The same machinery, unchanged, run on another design (north-star goal 3):
xorshift's `bdc_fused_*` units, from the committed yosys synthesis of the xorshift soak top
(`tools/fasm2lean3/fixture/xorshift_1.synth.json.xz`; the four routed seeds have byte-identical
synthesis, md5 9d030789...), extracted by `KERNEL=xorshift tools/compute/gen.sh`, compute for EVERY
input the operation bdc wrote:

| unit | bdc Verilog | theorem |
|---|---|---|
| uaddi0 | `e0 + 32'h1` | `xs_uaddi0_fn` = `Ops.addi 32 a 1` (`RipOK`, carry-in 1) |
| ucmpi0 | `slt(e1, e0)` (bdc's `>` on flipped sign bits) | `xs_ucmpi0_fn` (`SgtOK`) |
| ucmpi1 | `slt(e0, e1)` | `xs_ucmpi1_fn` (`SltOK`) |
| uxori2 | `e0 ^ (e0 << 5)` | `xs_uxori2_fn` (per-bit exhaustive over the computed support) |
| uxori1 | `t = e0 ^ (e0 << 13); t ^ (t >> 17)` | `xs_uxori1_fn` (per-bit exhaustive) |

Assumed / not covered: as for gcd_hw (`notes/C-hcf-compute.md`): primitive Boolean models, the
placed netlist (11g covers xorshift's import), timing, glitches.
-/

namespace Formal.Net.Compute.Xs
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.Xs

/-! ## uaddi0 -/

def addRip : Rip := ⟨(List.range 32).map (· + 38), [74, 78, 82, 86, 90, 94, 98], fun i => .inp 0 i, none,
  false, false, true, []⟩

abbrev AddBitX (i : Nat) : Prop :=
  NetOK Uaddi0.cells (addRip.cutset (i / 4)) (addRip.outs.getD i 0) (addRip.leaves (i / 4))
    (fun l => (addRip.sum (i / 4) l).testBit (i % 4))
abbrev AddCarX (j : Nat) : Prop :=
  NetOK Uaddi0.cells (addRip.cutset j) (addRip.cuts.getD j 0) (addRip.leaves j)
    (fun l => decide (16 ≤ addRip.sum j l))

set_option maxRecDepth 100000 in
theorem xa_b0 : AddBitX 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b1 : AddBitX 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b2 : AddBitX 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b3 : AddBitX 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b4 : AddBitX 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b5 : AddBitX 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b6 : AddBitX 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b7 : AddBitX 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b8 : AddBitX 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b9 : AddBitX 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b10 : AddBitX 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b11 : AddBitX 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b12 : AddBitX 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b13 : AddBitX 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b14 : AddBitX 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b15 : AddBitX 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b16 : AddBitX 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b17 : AddBitX 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b18 : AddBitX 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b19 : AddBitX 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b20 : AddBitX 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b21 : AddBitX 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b22 : AddBitX 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b23 : AddBitX 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b24 : AddBitX 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b25 : AddBitX 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b26 : AddBitX 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b27 : AddBitX 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b28 : AddBitX 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b29 : AddBitX 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b30 : AddBitX 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_b31 : AddBitX 31 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_c0 : AddCarX 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_c1 : AddCarX 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_c2 : AddCarX 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_c3 : AddCarX 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_c4 : AddCarX 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_c5 : AddCarX 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xa_c6 : AddCarX 6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem xa_ok : RipOK Uaddi0.cells addRip := by
  refine ⟨rfl, Uaddi0.nodup, fun i hi => ?_, fun j hj => ?_⟩
  · match i, hi with
    | 0, _ => exact xa_b0
    | 1, _ => exact xa_b1
    | 2, _ => exact xa_b2
    | 3, _ => exact xa_b3
    | 4, _ => exact xa_b4
    | 5, _ => exact xa_b5
    | 6, _ => exact xa_b6
    | 7, _ => exact xa_b7
    | 8, _ => exact xa_b8
    | 9, _ => exact xa_b9
    | 10, _ => exact xa_b10
    | 11, _ => exact xa_b11
    | 12, _ => exact xa_b12
    | 13, _ => exact xa_b13
    | 14, _ => exact xa_b14
    | 15, _ => exact xa_b15
    | 16, _ => exact xa_b16
    | 17, _ => exact xa_b17
    | 18, _ => exact xa_b18
    | 19, _ => exact xa_b19
    | 20, _ => exact xa_b20
    | 21, _ => exact xa_b21
    | 22, _ => exact xa_b22
    | 23, _ => exact xa_b23
    | 24, _ => exact xa_b24
    | 25, _ => exact xa_b25
    | 26, _ => exact xa_b26
    | 27, _ => exact xa_b27
    | 28, _ => exact xa_b28
    | 29, _ => exact xa_b29
    | 30, _ => exact xa_b30
    | 31, _ => exact xa_b31
    | _ + 32, h => exact absurd h (by omega)
  · match j, hj with
    | 0, _ => exact xa_c0
    | 1, _ => exact xa_c1
    | 2, _ => exact xa_c2
    | 3, _ => exact xa_c3
    | 4, _ => exact xa_c4
    | 5, _ => exact xa_c5
    | 6, _ => exact xa_c6
    | _ + 7, h => exact absurd h (by omega)

/-! ## ucmpi0 (signed greater-than), ucmpi1 (signed less-than) -/

def gsX0 : List SGrp :=
  [⟨0, 2, 83, 72, 8, 0⟩, ⟨2, 3, 84, 73, 8, 1⟩, ⟨5, 3, 85, 74, 8, 2⟩, ⟨8, 3, 86, 75, 8, 3⟩, ⟨11, 3, 87, 76, 17, 0⟩, ⟨14, 3, 88, 77, 17, 1⟩, ⟨17, 3, 89, 78, 17, 2⟩, ⟨20, 3, 90, 79, 17, 3⟩, ⟨23, 3, 91, 80, 24, 0⟩, ⟨26, 3, 92, 81, 24, 1⟩, ⟨29, 3, 93, 82, 24, 2⟩]
def gsX1 : List SGrp :=
  [⟨0, 2, 83, 72, 17, 0⟩, ⟨2, 3, 84, 73, 17, 1⟩, ⟨5, 3, 85, 74, 17, 2⟩, ⟨8, 3, 86, 75, 17, 3⟩, ⟨11, 3, 87, 76, 22, 0⟩, ⟨14, 3, 88, 77, 22, 1⟩, ⟨17, 3, 89, 78, 22, 2⟩, ⟨20, 3, 90, 79, 22, 3⟩, ⟨23, 3, 91, 80, 26, 0⟩, ⟨26, 3, 92, 81, 26, 1⟩, ⟨29, 3, 93, 82, 26, 2⟩]

set_option maxRecDepth 100000 in
theorem xc0_g0 : NetOK Ucmpi0.cells [] 83 (grpS 0 2) (eqSpecG 0 2) ∧
    NetOK Ucmpi0.cells [] 72 (grpS 0 2) (gtSpecG 0 2) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc0_g1 : NetOK Ucmpi0.cells [] 84 (grpS 2 3) (eqSpecG 2 3) ∧
    NetOK Ucmpi0.cells [] 73 (grpS 2 3) (gtSpecG 2 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc0_g2 : NetOK Ucmpi0.cells [] 85 (grpS 5 3) (eqSpecG 5 3) ∧
    NetOK Ucmpi0.cells [] 74 (grpS 5 3) (gtSpecG 5 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc0_g3 : NetOK Ucmpi0.cells [] 86 (grpS 8 3) (eqSpecG 8 3) ∧
    NetOK Ucmpi0.cells [] 75 (grpS 8 3) (gtSpecG 8 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc0_g4 : NetOK Ucmpi0.cells [] 87 (grpS 11 3) (eqSpecG 11 3) ∧
    NetOK Ucmpi0.cells [] 76 (grpS 11 3) (gtSpecG 11 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc0_g5 : NetOK Ucmpi0.cells [] 88 (grpS 14 3) (eqSpecG 14 3) ∧
    NetOK Ucmpi0.cells [] 77 (grpS 14 3) (gtSpecG 14 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc0_g6 : NetOK Ucmpi0.cells [] 89 (grpS 17 3) (eqSpecG 17 3) ∧
    NetOK Ucmpi0.cells [] 78 (grpS 17 3) (gtSpecG 17 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc0_g7 : NetOK Ucmpi0.cells [] 90 (grpS 20 3) (eqSpecG 20 3) ∧
    NetOK Ucmpi0.cells [] 79 (grpS 20 3) (gtSpecG 20 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc0_g8 : NetOK Ucmpi0.cells [] 91 (grpS 23 3) (eqSpecG 23 3) ∧
    NetOK Ucmpi0.cells [] 80 (grpS 23 3) (gtSpecG 23 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc0_g9 : NetOK Ucmpi0.cells [] 92 (grpS 26 3) (eqSpecG 26 3) ∧
    NetOK Ucmpi0.cells [] 81 (grpS 26 3) (gtSpecG 26 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc0_g10 : NetOK Ucmpi0.cells [] 93 (grpS 29 3) (eqSpecG 29 3) ∧
    NetOK Ucmpi0.cells [] 82 (grpS 29 3) (gtSpecG 29 3) := by decide +kernel

theorem xc0_grps : ∀ g ∈ gsX0, NetOK Ucmpi0.cells [] g.e (grpS g.lo g.len) (eqSpecG g.lo g.len) ∧
    NetOK Ucmpi0.cells [] g.d (grpS g.lo g.len) (gtSpecG g.lo g.len) := by
  intro g hg
  simp only [gsX0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact xc0_g0
  · exact xc0_g1
  · exact xc0_g2
  · exact xc0_g3
  · exact xc0_g4
  · exact xc0_g5
  · exact xc0_g6
  · exact xc0_g7
  · exact xc0_g8
  · exact xc0_g9
  · exact xc0_g10

set_option maxRecDepth 100000 in
theorem xc0_ok : SgtOK Ucmpi0.cells gsX0 71 :=
  ⟨Ucmpi0.nodup, by decide, by decide, xc0_grps, ⟨104, by decide, by decide +kernel⟩⟩


set_option maxRecDepth 100000 in
theorem xc1_g0 : NetOK Ucmpi1.cells [] 83 (grpS 0 2) (eqSpecG 0 2) ∧
    NetOK Ucmpi1.cells [] 72 (grpS 0 2) (gtSpecG 0 2) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_g1 : NetOK Ucmpi1.cells [] 84 (grpS 2 3) (eqSpecG 2 3) ∧
    NetOK Ucmpi1.cells [] 73 (grpS 2 3) (gtSpecG 2 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_g2 : NetOK Ucmpi1.cells [] 85 (grpS 5 3) (eqSpecG 5 3) ∧
    NetOK Ucmpi1.cells [] 74 (grpS 5 3) (gtSpecG 5 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_g3 : NetOK Ucmpi1.cells [] 86 (grpS 8 3) (eqSpecG 8 3) ∧
    NetOK Ucmpi1.cells [] 75 (grpS 8 3) (gtSpecG 8 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_g4 : NetOK Ucmpi1.cells [] 87 (grpS 11 3) (eqSpecG 11 3) ∧
    NetOK Ucmpi1.cells [] 76 (grpS 11 3) (gtSpecG 11 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_g5 : NetOK Ucmpi1.cells [] 88 (grpS 14 3) (eqSpecG 14 3) ∧
    NetOK Ucmpi1.cells [] 77 (grpS 14 3) (gtSpecG 14 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_g6 : NetOK Ucmpi1.cells [] 89 (grpS 17 3) (eqSpecG 17 3) ∧
    NetOK Ucmpi1.cells [] 78 (grpS 17 3) (gtSpecG 17 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_g7 : NetOK Ucmpi1.cells [] 90 (grpS 20 3) (eqSpecG 20 3) ∧
    NetOK Ucmpi1.cells [] 79 (grpS 20 3) (gtSpecG 20 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_g8 : NetOK Ucmpi1.cells [] 91 (grpS 23 3) (eqSpecG 23 3) ∧
    NetOK Ucmpi1.cells [] 80 (grpS 23 3) (gtSpecG 23 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_g9 : NetOK Ucmpi1.cells [] 92 (grpS 26 3) (eqSpecG 26 3) ∧
    NetOK Ucmpi1.cells [] 81 (grpS 26 3) (gtSpecG 26 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_g10 : NetOK Ucmpi1.cells [] 93 (grpS 29 3) (eqSpecG 29 3) ∧
    NetOK Ucmpi1.cells [] 82 (grpS 29 3) (gtSpecG 29 3) := by decide +kernel

theorem xc1_grps : ∀ g ∈ gsX1, NetOK Ucmpi1.cells [] g.e (grpS g.lo g.len) (eqSpecG g.lo g.len) ∧
    NetOK Ucmpi1.cells [] g.d (grpS g.lo g.len) (gtSpecG g.lo g.len) := by
  intro g hg
  simp only [gsX1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact xc1_g0
  · exact xc1_g1
  · exact xc1_g2
  · exact xc1_g3
  · exact xc1_g4
  · exact xc1_g5
  · exact xc1_g6
  · exact xc1_g7
  · exact xc1_g8
  · exact xc1_g9
  · exact xc1_g10
abbrev xc1FinR (c : Nat) : Prop :=
  LocalOKR (gsX1.map SGrp.e ++ [96]) (filt Ucmpi1.cells [71]).1 (.net 71)
    (gsX1.map (fun g => Leaf.cut g.e) ++ [.cut 96])
    (fun l => !(l.getD 11 false) && !((l.take 11).all id)) (c * 256) 256
set_option maxRecDepth 100000 in
theorem xc1_f0 : xc1FinR 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f1 : xc1FinR 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f2 : xc1FinR 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f3 : xc1FinR 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f4 : xc1FinR 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f5 : xc1FinR 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f6 : xc1FinR 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f7 : xc1FinR 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f8 : xc1FinR 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f9 : xc1FinR 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f10 : xc1FinR 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f11 : xc1FinR 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f12 : xc1FinR 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f13 : xc1FinR 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f14 : xc1FinR 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem xc1_f15 : xc1FinR 15 := by decide +kernel

set_option maxRecDepth 100000 in
theorem xc1_final : NetOK Ucmpi1.cells (gsX1.map SGrp.e ++ [96]) 71
    (gsX1.map (fun g => Leaf.cut g.e) ++ [.cut 96])
    (fun l => !(l.getD gsX1.length false) && !((l.take gsX1.length).all id)) := by
  refine ⟨localOK_of_ranges 16 256 (by decide) (fun c hc => ?_), by decide +kernel, by decide +kernel⟩
  match c, hc with
  | 0, _ => exact xc1_f0
  | 1, _ => exact xc1_f1
  | 2, _ => exact xc1_f2
  | 3, _ => exact xc1_f3
  | 4, _ => exact xc1_f4
  | 5, _ => exact xc1_f5
  | 6, _ => exact xc1_f6
  | 7, _ => exact xc1_f7
  | 8, _ => exact xc1_f8
  | 9, _ => exact xc1_f9
  | 10, _ => exact xc1_f10
  | 11, _ => exact xc1_f11
  | 12, _ => exact xc1_f12
  | 13, _ => exact xc1_f13
  | 14, _ => exact xc1_f14
  | 15, _ => exact xc1_f15
  | _ + 16, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem xc1_ok : SltOK Ucmpi1.cells gsX1 71 :=
  ⟨Ucmpi1.nodup, by decide, by decide, xc1_grps, ⟨96, by decide, xc1_final⟩⟩

end Formal.Net.Compute.Xs
