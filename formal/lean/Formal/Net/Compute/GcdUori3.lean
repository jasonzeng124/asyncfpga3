import Formal.Net.Compute.Slt
import Formal.Gen.Compute.GcdD.Uori3

/-!
# H_COMPUTE_FN for gcd_hw's `uori3`

Problem statement. This `bdc_fused_*` unit (bdc Verilog `z = ((e2 & e3) != 0) | slt(e0, e1)`; 1-bit `z`,
32-bit `e0, e1`, 1-bit `e2, e3`), as yosys synthesized it, computes
`Ops.ori 1 (Ops.cmpi .ne 1 (Ops.andi 1 c d) 0) (Ops.cmpi .slt 32 a b)` for EVERY `a, b, c, d`.

Proof: `SltOK` (signed comparator: 22 group LUTs checked exhaustively, the CARRY4 chain checked
structurally, the final LUT over the 11 equal-group nets and the last carry), `slt_sound`, then
the output, with the comparator output as a cut point, checked exhaustively.

Assumed / not covered: LUT, CARRY4 Boolean semantics (shard A's models); that this is the placed
netlist (11f/11g); timing; glitches.
-/

namespace Formal.Net.Compute.GcdD
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.GcdD

/-- The comparator groups (found by `tools/compute/sltcert.py`; checked below). -/
def gsO_uori3 : List SGrp :=
  [⟨0, 2, 90, 89, 19, 0⟩, ⟨2, 3, 91, 88, 19, 1⟩, ⟨5, 3, 92, 87, 19, 2⟩, ⟨8, 3, 93, 86, 19, 3⟩, ⟨11, 3, 94, 85, 24, 0⟩, ⟨14, 3, 95, 84, 24, 1⟩, ⟨17, 3, 96, 83, 24, 2⟩, ⟨20, 3, 97, 82, 24, 3⟩, ⟨23, 3, 98, 81, 28, 0⟩, ⟨26, 3, 99, 80, 28, 1⟩, ⟨29, 3, 100, 79, 28, 2⟩]

set_option maxRecDepth 100000 in
theorem uori3_g0 : NetOK Uori3.cells [] 90 (grpS 0 2) (eqSpecG 0 2) ∧
    NetOK Uori3.cells [] 89 (grpS 0 2) (gtSpecG 0 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_g1 : NetOK Uori3.cells [] 91 (grpS 2 3) (eqSpecG 2 3) ∧
    NetOK Uori3.cells [] 88 (grpS 2 3) (gtSpecG 2 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_g2 : NetOK Uori3.cells [] 92 (grpS 5 3) (eqSpecG 5 3) ∧
    NetOK Uori3.cells [] 87 (grpS 5 3) (gtSpecG 5 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_g3 : NetOK Uori3.cells [] 93 (grpS 8 3) (eqSpecG 8 3) ∧
    NetOK Uori3.cells [] 86 (grpS 8 3) (gtSpecG 8 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_g4 : NetOK Uori3.cells [] 94 (grpS 11 3) (eqSpecG 11 3) ∧
    NetOK Uori3.cells [] 85 (grpS 11 3) (gtSpecG 11 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_g5 : NetOK Uori3.cells [] 95 (grpS 14 3) (eqSpecG 14 3) ∧
    NetOK Uori3.cells [] 84 (grpS 14 3) (gtSpecG 14 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_g6 : NetOK Uori3.cells [] 96 (grpS 17 3) (eqSpecG 17 3) ∧
    NetOK Uori3.cells [] 83 (grpS 17 3) (gtSpecG 17 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_g7 : NetOK Uori3.cells [] 97 (grpS 20 3) (eqSpecG 20 3) ∧
    NetOK Uori3.cells [] 82 (grpS 20 3) (gtSpecG 20 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_g8 : NetOK Uori3.cells [] 98 (grpS 23 3) (eqSpecG 23 3) ∧
    NetOK Uori3.cells [] 81 (grpS 23 3) (gtSpecG 23 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_g9 : NetOK Uori3.cells [] 99 (grpS 26 3) (eqSpecG 26 3) ∧
    NetOK Uori3.cells [] 80 (grpS 26 3) (gtSpecG 26 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_g10 : NetOK Uori3.cells [] 100 (grpS 29 3) (eqSpecG 29 3) ∧
    NetOK Uori3.cells [] 79 (grpS 29 3) (gtSpecG 29 3) := by decide +kernel

theorem uori3_grps : ∀ g ∈ gsO_uori3, NetOK Uori3.cells [] g.e (grpS g.lo g.len) (eqSpecG g.lo g.len) ∧
    NetOK Uori3.cells [] g.d (grpS g.lo g.len) (gtSpecG g.lo g.len) := by
  intro g hg
  simp only [gsO_uori3, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact uori3_g0
  · exact uori3_g1
  · exact uori3_g2
  · exact uori3_g3
  · exact uori3_g4
  · exact uori3_g5
  · exact uori3_g6
  · exact uori3_g7
  · exact uori3_g8
  · exact uori3_g9
  · exact uori3_g10

abbrev uori3FinR (c : Nat) : Prop :=
  LocalOKR (gsO_uori3.map SGrp.e ++ [103]) (filt Uori3.cells [78]).1 (.net 78) (gsO_uori3.map (fun g => Leaf.cut g.e) ++ [.cut 103]) (fun l => !(l.getD 11 false) && !((l.take 11).all id)) (c * 256) 256

set_option maxRecDepth 100000 in
theorem uori3_f0 : uori3FinR 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f1 : uori3FinR 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f2 : uori3FinR 2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f3 : uori3FinR 3 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f4 : uori3FinR 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f5 : uori3FinR 5 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f6 : uori3FinR 6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f7 : uori3FinR 7 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f8 : uori3FinR 8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f9 : uori3FinR 9 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f10 : uori3FinR 10 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f11 : uori3FinR 11 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f12 : uori3FinR 12 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f13 : uori3FinR 13 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f14 : uori3FinR 14 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_f15 : uori3FinR 15 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uori3_final : NetOK Uori3.cells (gsO_uori3.map SGrp.e ++ [103]) 78 (gsO_uori3.map (fun g => Leaf.cut g.e) ++ [.cut 103])
    (fun l => !(l.getD gsO_uori3.length false) && !((l.take gsO_uori3.length).all id)) := by
  refine ⟨localOK_of_ranges 16 256 (by decide) (fun c hc => ?_), by decide +kernel, by decide +kernel⟩
  match c, hc with
  | 0, _ => exact uori3_f0
  | 1, _ => exact uori3_f1
  | 2, _ => exact uori3_f2
  | 3, _ => exact uori3_f3
  | 4, _ => exact uori3_f4
  | 5, _ => exact uori3_f5
  | 6, _ => exact uori3_f6
  | 7, _ => exact uori3_f7
  | 8, _ => exact uori3_f8
  | 9, _ => exact uori3_f9
  | 10, _ => exact uori3_f10
  | 11, _ => exact uori3_f11
  | 12, _ => exact uori3_f12
  | 13, _ => exact uori3_f13
  | 14, _ => exact uori3_f14
  | 15, _ => exact uori3_f15
  | _ + 16, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem uori3_slt : SltOK Uori3.cells gsO_uori3 78 :=
  ⟨Uori3.nodup, by decide, by decide, uori3_grps, ⟨103, by decide, uori3_final⟩⟩

set_option maxRecDepth 100000 in
theorem uori3_out : NetOK Uori3.cells [78] 75 [.cut 78, .inp 2 0, .inp 3 0]
    (fun l => (l.getD 1 false && l.getD 2 false) || l.getD 0 false) := by decide +kernel

/-- **uori3 computes `((e2 & e3) != 0) | slt(e0, e1)`** for every input. -/
theorem uori3_fn (a b c d : Nat) :
    unitVal Uori3.cells Uori3.outs [a, b, c, d] =
      Ops.ori 1 (Ops.cmpi .ne 1 (Ops.andi 1 c d) 0) (Ops.cmpi .slt 32 a b) := by
  have hslt := slt_sound uori3_slt [a, b, c, d]
  obtain ⟨o1, o2, o3⟩ := uori3_out
  have hv := cert_val Uori3.nodup o1 o2 o3 (inEnv [a, b, c, d])
  have hslt' : run (inEnv [a, b, c, d]) [] Uori3.cells (fun _ => false) 78 =
      decide (Ops.flip 32 a < Ops.flip 32 b) := hslt
  simp only [List.map, cutEnv, hslt', inEnv, List.getD_cons_zero, List.getD_cons_succ] at hv
  unfold unitVal
  simp only [show Uori3.outs.length = 1 from rfl, word, Nat.zero_or]
  show (if run (inEnv [a, b, c, d]) [] Uori3.cells (fun _ => false) 75 then 2 ^ 0 else 0) = _
  rw [hv]
  simp only [Ops.ori, Ops.cmpi, Ops.andi, Ops.b2n, Nat.pow_one, Nat.mod_mod, Nat.zero_mod]
  rw [mod_two_eq_testBit (c &&& d), Nat.testBit_and]
  by_cases h : Ops.flip 32 a < Ops.flip 32 b <;>
    rcases Bool.eq_false_or_eq_true (c.testBit 0) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (d.testBit 0) with h2 | h2 <;>
    simp [h, h1, h2]

end Formal.Net.Compute.GcdD
