import Formal.Core.Substrate.Real
import Formal.Core.Delay.CornerDiff
open Formal.Core.Substrate Formal.Core.CornerDiff Formal.Core.Corner
local notation "Scat" => Formal.Core.Corner.Scat

/-! ### endpoints_sound_real -/
#check @endpoints_sound_real

def k10 : Kappa := ⟨1, 10, by decide, by decide⟩
def k0 : Kappa := ⟨0, 1, by decide, by decide⟩
def Dx : CArc := ⟨100, 200, by decide⟩
def Rx : CArc := ⟨200, 400, by decide⟩

theorem ep_ok : EndpointOK k10 Dx Rx 10 := by decide

-- Joint satisfiability: all hypotheses at c = 1/2, kappa = 1/10, real delays 150 / 300.
theorem ep_instance : (150 : ℝ) + (10:ℕ) ≤ 300 := by
  have hk : k10.toReal = 1/10 := by simp [Kappa.toReal, k10]
  have hD : Scat k10.toReal (Dx.toArc.at' (1/2)) 150 := by
    rw [hk]; simp [Formal.Core.Corner.Scat, Arc.at', lerp, CArc.toArc, Dx]; norm_num
  have hR : Scat k10.toReal (Rx.toArc.at' (1/2)) 300 := by
    rw [hk]; simp [Formal.Core.Corner.Scat, Arc.at', lerp, CArc.toArc, Rx]; norm_num
  exact endpoints_sound_real ep_ok (by norm_num) (by norm_num) hD hR

-- Without EndpointOK the conclusion fails (D = R = [100,100], m = 10, delays 100).
def E100 : CArc := ⟨100, 100, by decide⟩
theorem ep_drop_check :
    ¬ EndpointOK k0 E100 E100 10 ∧ Scat k0.toReal (E100.toArc.at' (1/2)) 100 ∧
      ¬ ((100:ℝ) + (10:ℕ) ≤ 100) := by
  refine ⟨by decide, ?_, by norm_num⟩
  simp [Formal.Core.Corner.Scat, Kappa.toReal, k0, Arc.at', lerp, CArc.toArc, E100]; norm_num

-- Without c ≤ 1 (extrapolated corner c = 3) the conclusion fails although EndpointOK holds.
def Dy : CArc := ⟨100, 200, by decide⟩
def Ry : CArc := ⟨150, 210, by decide⟩
theorem ep_drop_c1 : EndpointOK k0 Dy Ry 0 ∧
    Scat k0.toReal (Dy.toArc.at' 3) 400 ∧ Scat k0.toReal (Ry.toArc.at' 3) 330 ∧
    ¬ ((400:ℝ) + (0:ℕ) ≤ 330) := by
  refine ⟨by decide, ?_, ?_, by norm_num⟩ <;>
    simp [Formal.Core.Corner.Scat, Kappa.toReal, k0, Arc.at', lerp, CArc.toArc, Dy, Ry] <;> norm_num

/-! ### ruleE_sound_diff -/
#check @ruleE_sound_diff
-- Instance at the boundary kd = kappaE, s = 1, Ps = 1, Pr = 2, as = 0, ar = 1.
theorem rE_instance : (0:ℝ) + 0 < 0 + 1 :=
  ruleE_sound_diff (κd := kappaE) (s := 1) (Pr := 2) (Ps := 1) one_pos le_rfl (by norm_num)
    (by unfold DiffLow kappaE; norm_num) (by unfold guardLo guardHi; norm_num)
-- Dropping the guard: Ps = Pr = 1, kd = 0, as = ar = 0 meets DiffLow but not the conclusion.
theorem rE_drop_guard : DiffLow 0 1 1 1 0 0 ∧ ¬ (0 < guardLo * 1 - guardHi * 1) ∧
    ¬ ((0:ℝ) + 0 < 0 + 0) := by
  refine ⟨by unfold DiffLow; norm_num, by unfold guardLo guardHi; norm_num, by norm_num⟩

/-! ### diff_not_imp_scat: the library witness is degenerate -/
#check @diff_not_imp_scat
-- Their witness (s=1, Pa=Pb=1, da=db=|K|+3) has per-path scatter ZERO at another scale:
-- at s' = |K|+3 both tails satisfy Scat 0 and DiffScat 0 still holds.
theorem witness_is_scale_artifact (K : ℝ) :
    let s' := |K| + 3
    DiffScat 0 s' 1 1 (|K|+3) (|K|+3) ∧ Scat 0 (s' * 1) (|K|+3) ∧ Scat 0 (s' * 1) (|K|+3) := by
  intro s'
  refine ⟨?_, ?_, ?_⟩ <;> simp [DiffScat, Formal.Core.Corner.Scat, s']

-- A non-degenerate version: a GUARDED pair (Ps = 1, Pr = 2) with kd = 0 at scale 1 whose
-- per-path scatter exceeds K at EVERY positive shared scale (for 0 ≤ K < 1).
theorem diff_not_imp_scat_strong (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) :
    ∃ da db : ℝ, 0 < guardLo * 2 - guardHi * 1 ∧ DiffScat 0 1 1 2 da db ∧
      ∀ s' : ℝ, 0 < s' → ¬ (Scat K (s' * 1) da ∧ Scat K (s' * 2) db) := by
  set e := (1 - K) / (4 * (1 + K)) with he
  have hpos : 0 < 1 + K := by linarith
  have he4 : (1 + K) * (4 * e) = 1 - K := by rw [he]; field_simp
  have he0 : 0 < e := by rw [he]; apply div_pos <;> linarith
  refine ⟨e, 1 + e, by unfold guardLo guardHi; norm_num, ?_, ?_⟩
  · constructor <;> linarith
  · rintro s' hs' ⟨⟨h1, _⟩, ⟨_, h4⟩⟩
    -- (1-K) s' ≤ e and 1+e ≤ (1+K) 2 s'  ⇒  (1-K)(1+e) ≤ 2(1+K)e·... contradiction
    have a : (1 - K) * (1 + e) ≤ (1 - K) * ((1 + K) * (s' * 2)) :=
      mul_le_mul_of_nonneg_left h4 (by linarith)
    have b : (1 + K) * 2 * ((1 - K) * (s' * 1)) ≤ (1 + K) * 2 * e :=
      mul_le_mul_of_nonneg_left h1 (by nlinarith)
    nlinarith

/-! ### ring_kappa_iff -/
#check @ring_kappa_iff
example : ∃ s : ℝ, Scat (697/2243) s (1470/1000) ∧ Scat (697/2243) s (773/1000) :=
  (ring_kappa_iff (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)
example : ¬ ∃ s : ℝ, Scat (3/10) s (1470/1000) ∧ Scat (3/10) s (773/1000) := by
  rw [ring_kappa_iff (by norm_num) (by norm_num) (by norm_num)]; norm_num
