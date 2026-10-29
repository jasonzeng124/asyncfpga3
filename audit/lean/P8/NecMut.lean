import Formal.Cells.Necessity2Arb
-- MUTATION (expected to FAIL): give g1's route 1 ps less (wr1g 16 -> 15, so RT2.g1 holds);
-- the same signals must then NOT be a Run (otherwise the theorem would be false).
namespace Audit.P8.NecMut
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2 Formal.Cells.Necessity2Arb
def DG1m : Dl := dN 15 0 6 0 0 1 0 0 0 2 1 8 (by omega)
theorem m : Run DG1m SG1 where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [SG1, DG1m, dN, A0w, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1, DG1m, dN, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1, DG1m, dN, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1, DG1m, dN, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1, DG1m, dN, A0w, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1, DG1m, dN, A0w, CE_eq]; omega
  H_SRV := srv_7h SG1 rfl (by decide) (by decide) (by decide)
-- and the run genuinely is not a Run with the field met: prove the negation
theorem m_neg : ¬ Run DG1m SG1 := fun R => by
  have := R.H_g1 16; revert this; simp [SG1, DG1m, dN, FG1_eq]
end Audit.P8.NecMut
