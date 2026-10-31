import Formal.Net.Compute.GcdUori2
import Formal.Net.Compute.GcdShli0K0
/-! Auditor P15bc: negative controls for the NEW certificate kinds (formal's Wip/Chcf/Neg.lean only
mutates uori0 (BitLocal) and uaddi0 (AddOK slice), kinds already audited in P14).
(1) Slt: in uori2, exchange e0 bit 31 and e1 bit 31 at every LUT pin (the signed compare becomes
    an unsigned one on the sign bit). The top group's D-LUT check must fail.
(2) FixShOK: in ushli0, swap pins I2/I3 (shift-amount bits 3 and 2) of the LUT driving net 76.
    The auditor's Python simulation (BC_netcmp2) shows this changes output bit 5 for k in {4,5,8,9}.
    The k = 4, bit 5 check must fail; the k = 0, bit 5 check must still hold. -/
open Formal.Net.Compute Formal.Net.Compute.GcdD Formal.Gen.Compute.GcdD

def swW : W → W
  | .inp 0 31 => .inp 1 31
  | .inp 1 31 => .inp 0 31
  | w => w
def uori2Sw : List Cell := Uori2.cells.map fun c => match c with
  | .lut i ins o => .lut i (ins.map swW) o
  | c => c

set_option maxRecDepth 100000 in
theorem aud_uori2_orig_gt : NetOK Uori2.cells [] 79 (grpS 29 3) (gtSpecG 29 3) := by decide +kernel
set_option maxRecDepth 100000 in
theorem aud_uori2_sw_rejected : ¬ NetOK uori2Sw [] 79 (grpS 29 3) (gtSpecG 29 3) := by decide +kernel

def ushMut : List Cell := Ushli0.cells.map fun c => match c with
  | .lut i [a, b, .inp 1 3, .inp 1 2, e] 76 => .lut i [a, b, .inp 1 2, .inp 1 3, e] 76
  | c => c

abbrev ShlBitM (k i : Nat) : Prop :=
  let w := Ushli0.outs.getD i .c0
  let S := dedup (afOf (fixK k) [] (coneW ushMut w) w).supp
  LocalOKF [] (coneW ushMut w) w S (fixK k)
      (fun l => match shlSrc k i with
        | some j => l.getD (S.idxOf (.inp 0 j)) false
        | none => false) ∧
    S.all (fun l => (fixK k l).isNone) = true ∧
    (match shlSrc k i with
     | some j => decide (Leaf.inp 0 j ∈ S)
     | none => true) = true

theorem aud_ushMut_changed : ((ushMut.map Cell.ins) != (Ushli0.cells.map Cell.ins)) = true := by decide +kernel
-- the original passes the same check: formal's GcdShli0K0.shl_k4_b5
#check @shl_k4_b5
set_option maxRecDepth 100000 in
theorem aud_ush_mut_k0_b5_holds : ShlBitM 0 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem aud_ush_mut_k4_b5_rejected : ¬ ShlBitM 4 5 := by decide +kernel

#print axioms aud_uori2_sw_rejected
#print axioms aud_ush_mut_k4_b5_rejected
