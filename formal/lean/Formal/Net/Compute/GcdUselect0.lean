import Formal.Net.Compute.Slt
import Formal.Gen.Compute.GcdD.Uselect0

/-!
# H_COMPUTE_FN for gcd_hw's `uselect0`

Problem statement. This `bdc_fused_*` unit (bdc Verilog `z = slt(e0, e1) ? e0 : e1`, 32 bits), as yosys
synthesized it, computes `(if slt(a, b) then a else b) mod 2^32` for EVERY `a, b`.

Proof: `SltOK` (signed comparator: 22 group LUTs checked exhaustively, the CARRY4 chain checked
structurally, the final LUT over the 11 equal-group nets and the last carry), `slt_sound`, then
the output, with the comparator output as a cut point, checked exhaustively.

Assumed / not covered: LUT, CARRY4 Boolean semantics (shard A's models); that this is the placed
netlist (11f/11g); timing; glitches.
-/

namespace Formal.Net.Compute.GcdD
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.GcdD

/-- The comparator groups (found by `tools/compute/sltcert.py`; checked below). -/
def gsS_uselect0 : List SGrp :=
  [⟨0, 2, 114, 103, 17, 0⟩, ⟨2, 3, 115, 104, 17, 1⟩, ⟨5, 3, 116, 105, 17, 2⟩, ⟨8, 3, 117, 106, 17, 3⟩, ⟨11, 3, 118, 107, 22, 0⟩, ⟨14, 3, 119, 108, 22, 1⟩, ⟨17, 3, 120, 109, 22, 2⟩, ⟨20, 3, 121, 110, 22, 3⟩, ⟨23, 3, 122, 111, 26, 0⟩, ⟨26, 3, 123, 112, 26, 1⟩, ⟨29, 3, 124, 113, 26, 2⟩]

set_option maxRecDepth 100000 in
theorem uselect0_g0 : NetOK Uselect0.cells [] 114 (grpS 0 2) (eqSpecG 0 2) ∧
    NetOK Uselect0.cells [] 103 (grpS 0 2) (gtSpecG 0 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_g1 : NetOK Uselect0.cells [] 115 (grpS 2 3) (eqSpecG 2 3) ∧
    NetOK Uselect0.cells [] 104 (grpS 2 3) (gtSpecG 2 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_g2 : NetOK Uselect0.cells [] 116 (grpS 5 3) (eqSpecG 5 3) ∧
    NetOK Uselect0.cells [] 105 (grpS 5 3) (gtSpecG 5 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_g3 : NetOK Uselect0.cells [] 117 (grpS 8 3) (eqSpecG 8 3) ∧
    NetOK Uselect0.cells [] 106 (grpS 8 3) (gtSpecG 8 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_g4 : NetOK Uselect0.cells [] 118 (grpS 11 3) (eqSpecG 11 3) ∧
    NetOK Uselect0.cells [] 107 (grpS 11 3) (gtSpecG 11 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_g5 : NetOK Uselect0.cells [] 119 (grpS 14 3) (eqSpecG 14 3) ∧
    NetOK Uselect0.cells [] 108 (grpS 14 3) (gtSpecG 14 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_g6 : NetOK Uselect0.cells [] 120 (grpS 17 3) (eqSpecG 17 3) ∧
    NetOK Uselect0.cells [] 109 (grpS 17 3) (gtSpecG 17 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_g7 : NetOK Uselect0.cells [] 121 (grpS 20 3) (eqSpecG 20 3) ∧
    NetOK Uselect0.cells [] 110 (grpS 20 3) (gtSpecG 20 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_g8 : NetOK Uselect0.cells [] 122 (grpS 23 3) (eqSpecG 23 3) ∧
    NetOK Uselect0.cells [] 111 (grpS 23 3) (gtSpecG 23 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_g9 : NetOK Uselect0.cells [] 123 (grpS 26 3) (eqSpecG 26 3) ∧
    NetOK Uselect0.cells [] 112 (grpS 26 3) (gtSpecG 26 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_g10 : NetOK Uselect0.cells [] 124 (grpS 29 3) (eqSpecG 29 3) ∧
    NetOK Uselect0.cells [] 113 (grpS 29 3) (gtSpecG 29 3) := by decide +kernel

theorem uselect0_grps : ∀ g ∈ gsS_uselect0, NetOK Uselect0.cells [] g.e (grpS g.lo g.len) (eqSpecG g.lo g.len) ∧
    NetOK Uselect0.cells [] g.d (grpS g.lo g.len) (gtSpecG g.lo g.len) := by
  intro g hg
  simp only [gsS_uselect0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact uselect0_g0
  · exact uselect0_g1
  · exact uselect0_g2
  · exact uselect0_g3
  · exact uselect0_g4
  · exact uselect0_g5
  · exact uselect0_g6
  · exact uselect0_g7
  · exact uselect0_g8
  · exact uselect0_g9
  · exact uselect0_g10

abbrev uselect0FinR (c : Nat) : Prop :=
  LocalOKR (gsS_uselect0.map SGrp.e ++ [128]) (filt Uselect0.cells [125]).1 (.net 125) (gsS_uselect0.map (fun g => Leaf.cut g.e) ++ [.cut 128]) (fun l => !(l.getD 11 false) && !((l.take 11).all id)) (c * 256) 256

set_option maxRecDepth 100000 in
theorem uselect0_f0 : uselect0FinR 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f1 : uselect0FinR 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f2 : uselect0FinR 2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f3 : uselect0FinR 3 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f4 : uselect0FinR 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f5 : uselect0FinR 5 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f6 : uselect0FinR 6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f7 : uselect0FinR 7 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f8 : uselect0FinR 8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f9 : uselect0FinR 9 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f10 : uselect0FinR 10 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f11 : uselect0FinR 11 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f12 : uselect0FinR 12 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f13 : uselect0FinR 13 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f14 : uselect0FinR 14 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_f15 : uselect0FinR 15 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uselect0_final : NetOK Uselect0.cells (gsS_uselect0.map SGrp.e ++ [128]) 125 (gsS_uselect0.map (fun g => Leaf.cut g.e) ++ [.cut 128])
    (fun l => !(l.getD gsS_uselect0.length false) && !((l.take gsS_uselect0.length).all id)) := by
  refine ⟨localOK_of_ranges 16 256 (by decide) (fun c hc => ?_), by decide +kernel, by decide +kernel⟩
  match c, hc with
  | 0, _ => exact uselect0_f0
  | 1, _ => exact uselect0_f1
  | 2, _ => exact uselect0_f2
  | 3, _ => exact uselect0_f3
  | 4, _ => exact uselect0_f4
  | 5, _ => exact uselect0_f5
  | 6, _ => exact uselect0_f6
  | 7, _ => exact uselect0_f7
  | 8, _ => exact uselect0_f8
  | 9, _ => exact uselect0_f9
  | 10, _ => exact uselect0_f10
  | 11, _ => exact uselect0_f11
  | 12, _ => exact uselect0_f12
  | 13, _ => exact uselect0_f13
  | 14, _ => exact uselect0_f14
  | 15, _ => exact uselect0_f15
  | _ + 16, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem uselect0_slt : SltOK Uselect0.cells gsS_uselect0 125 :=
  ⟨Uselect0.nodup, by decide, by decide, uselect0_grps, ⟨128, by decide, uselect0_final⟩⟩

abbrev SelBit (i : Nat) : Prop :=
  Uselect0.outs.getD i .c0 = .net (outNet Uselect0.outs i) ∧
  NetOK Uselect0.cells [125] (outNet Uselect0.outs i) [.cut 125, .inp 0 i, .inp 1 i]
    (fun l => if l.getD 0 false then l.getD 1 false else l.getD 2 false)

set_option maxRecDepth 100000 in
theorem uselect0_bits : ∀ i, i < 32 → SelBit i := by decide +kernel

/-- **uselect0 computes `slt(e0, e1) ? e0 : e1`** (32 bits) for every input. -/
theorem uselect0_fn (a b : Nat) :
    unitVal Uselect0.cells Uselect0.outs [a, b] =
      (if Ops.flip 32 a < Ops.flip 32 b then a else b) % 2 ^ 32 := by
  have hslt : run (inEnv [a, b]) [] Uselect0.cells (fun _ => false) 125 =
      decide (Ops.flip 32 a < Ops.flip 32 b) := slt_sound uselect0_slt [a, b]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_unitVal, show Uselect0.outs.length = 32 from rfl, Nat.testBit_mod_two_pow]
  by_cases hi : i < 32
  · simp only [hi, decide_true, Bool.true_and]
    obtain ⟨hw, o1, o2, o3⟩ := uselect0_bits i hi
    have hv := cert_val Uselect0.nodup o1 o2 o3 (inEnv [a, b])
    simp only [List.map, cutEnv, hslt, inEnv, List.getD_cons_zero, List.getD_cons_succ] at hv
    rw [hw]
    show run (inEnv [a, b]) [] Uselect0.cells (fun _ => false) _ = _
    rw [hv]
    by_cases h : Ops.flip 32 a < Ops.flip 32 b <;> simp [h]
  · simp [hi]

end Formal.Net.Compute.GcdD
