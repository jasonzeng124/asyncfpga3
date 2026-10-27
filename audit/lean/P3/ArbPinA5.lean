import Formal.Cells.ArbCorners

/-!
# Audit P3: ArbCorners' O5 numbers are pin-assignment specific

ArbCorners takes the q -> g1 arc from `SLICEL/A5LUT IOPATH A3 O5` (42/150,
"I2 under the identity pin map"). In the formal repo's OWN routed arbiters
(`Formal/Net/FasmLink/S1..S4`, read back from the bitstreams), nextpnr put q
on ugrant's physical pin A5 in 3 of 4 seeds (S1, S3, S4; S2: A3), and ugrant
sits in CLBLM_R SLICEM ALUT. prjxray-db zynq7 `CLBLM_R.sdf`, SLICEM/A5LUT:

    (IOPATH A1 O5 (0.044::0.055)(0.121::0.150))
    (IOPATH A5 O5 (0.048::0.060)(0.093::0.116))

so at SLOW_MAX o5q = 116 < o6 = 124 and at FAST_MIN o5q = 48 > o6 = 45: the
sign of `o6 - o5q`, on which the structural-RT1/RT1b, skew-cap and rule-J
"conservative" statements rest, is the OPPOSITE of ArbCorners' at both corners.
-/

namespace Audit.P3.PinA5
open Formal.Cells Formal.Cells.ArbCorners Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2

/-- SLOW_MAX with q on physical pin A5 (CLBLM_R SLICEM A5LUT), r1/r2 on A1/A4 (150). -/
def slowA5 : Corner := ⟨124, 150, 116, by decide⟩
/-- FAST_MIN with q on A5. -/
def fastA5 : Corner := ⟨45, 44, 48, by decide⟩

/-- A routing with a long g2 -> ua? path (`wr2g = 1000`), everything else 0. -/
def xLong : Rt := ⟨0, 0, 0, 1000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, by decide⟩

/-- `rt1b_slow_structural` says RT1b holds at SLOW_MAX for EVERY routing
(identity pin map). With q on A5 it fails for this routing. -/
theorem rt1b_slow_not_structural_A5 :
    RT1b (cDl slowMax RF.sym xLong) ∧ ¬ RT1b (cDl slowA5 RF.sym xLong) := by
  refine ⟨rt1b_slow_structural xLong, ?_⟩
  rw [RT1b_iff, (decomp _ _ _).2.2.2.2.2.2.2.1, (decomp _ _ _).2.2.2.2.2.2.2.2.1]
  simp [slowA5, RF.sym, wRT1b, xLong]

/-- `rt1_fast_structural` says RT1 holds at FAST_MIN for every routing; with q on
A5 its structural disjunct is false (45 < 48), so RT1 reduces to the race. -/
theorem rt1_fast_not_structural_A5 :
    ¬ (0 ≤ mRT1s (cDl fastA5 RF.sym xLong)) := by
  rw [(decomp _ _ _).2.1]; simp [fastA5, RF.sym]

/-- Rule J, client 1, SLOW_MAX: the true early-side arcs are O6 + O5(A5) =
240 < 248 = rule J's flat 2 x 124. Rule J is then 8 ps OPTIMISTIC, not
"26 ps conservative". -/
theorem ruleJ_client1_A5 : O6.smax + 116 = 240 ∧ (240 : Int) < 124 + 124 := by decide

/-- Skew caps at SLOW_MAX flip: r2 -> r1 cap 8 ps (ArbCorners: 0), r1 -> r2 0 (ArbCorners: 26). -/
theorem caps_A5 : max 0 (slowA5.o6 - slowA5.o5q) = 8 ∧ max 0 (slowA5.o5q - slowA5.o6) = 0 := by
  decide

end Audit.P3.PinA5

#print axioms Audit.P3.PinA5.rt1b_slow_not_structural_A5
#print axioms Audit.P3.PinA5.rt1_fast_not_structural_A5
