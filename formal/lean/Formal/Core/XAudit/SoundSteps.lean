import Formal.Core.XAudit.Parse

/-!
# Formal.Core.XAudit.SoundSteps — what the parser's ps → step rounding guarantees

Probe XSound2 (shard A). See `formal/notes/A-xsound2.md`.

The continuous-time soundness theorems (`XSimChanReal.sound_real`,
`XAudit.SoundPhys`) need, for every gate with physical band `[L, H]` (ps) and
step band `[lo, hi]` at unit `u` ps: `lo · u ≤ L` and `H ≤ hi · u`. The parser
(`Parse.toSteps`, TRUSTED code, but a pure function we can reason about)
computes `lo = max 1 ⌊L/u⌋`, `hi = max lo ⌈H/u⌉` and a flag `raised = (⌊L/u⌋ = 0)`.

* `toSteps_lo_le`: if `u ≤ L` (the flag is not set), `lo · u ≤ L`;
* `toSteps_hi_ge`: always `H ≤ hi · u`;
* `toSteps_raised_iff`: the flag is set exactly when `L < u`; then `lo = 1`
  and `lo · u = u > L` (`toSteps_raised_lo`): the side condition FAILS, and the
  continuous-time theorems do NOT cover that gate. The executable lists these
  arcs ("NOTE lo < 1 step raised to 1 step"); a run whose list is non-empty is
  not covered by them (choose a smaller `unit_ps`, or fold the sub-unit arc into
  its reader's band).
* `toSteps_lo_pos`, `toSteps_lo_le_hi`: `1 ≤ lo ≤ hi` (the `Design.WF` bounds).
-/

namespace Formal.Core.XAudit.SoundSteps

open Formal.Core.XAudit.Parse

theorem toSteps_fst (u L H : Nat) : (toSteps u (L, H)).1 = max 1 (L / u) := rfl
theorem toSteps_snd (u L H : Nat) :
    (toSteps u (L, H)).2.1 = max (max 1 (L / u)) ((H + u - 1) / u) := rfl
theorem toSteps_flag (u L H : Nat) : (toSteps u (L, H)).2.2 = (L / u == 0) := rfl

theorem toSteps_lo_le {u L H : Nat} (hu : 0 < u) (hL : u ≤ L) :
    (toSteps u (L, H)).1 * u ≤ L := by
  rw [toSteps_fst]
  have h1 : 1 ≤ L / u := (Nat.le_div_iff_mul_le hu).2 (by omega)
  rw [Nat.max_eq_right h1]
  exact Nat.div_mul_le_self L u

theorem ceil_mul_ge {u H : Nat} (hu : 0 < u) : H ≤ (H + u - 1) / u * u := by
  have h1 := Nat.div_add_mod (H + u - 1) u
  have h2 := Nat.mod_lt (H + u - 1) hu
  rw [Nat.mul_comm] at h1
  generalize (H + u - 1) / u * u = P at h1 ⊢
  omega

theorem toSteps_hi_ge {u L H : Nat} (hu : 0 < u) : H ≤ (toSteps u (L, H)).2.1 * u := by
  rw [toSteps_snd]
  exact Nat.le_trans (ceil_mul_ge hu) (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))

theorem toSteps_raised_iff {u L H : Nat} (hu : 0 < u) :
    (toSteps u (L, H)).2.2 = true ↔ L < u := by
  rw [toSteps_flag, beq_iff_eq, Nat.div_eq_zero_iff_lt hu]

theorem toSteps_raised_lo {u L H : Nat} (hu : 0 < u) (hL : L < u) :
    (toSteps u (L, H)).1 = 1 ∧ L < (toSteps u (L, H)).1 * u := by
  rw [toSteps_fst, (Nat.div_eq_zero_iff_lt hu).2 hL]
  exact ⟨rfl, by simpa using hL⟩

theorem toSteps_lo_pos (u L H : Nat) : 1 ≤ (toSteps u (L, H)).1 := by
  rw [toSteps_fst]; exact Nat.le_max_left _ _

theorem toSteps_lo_le_hi (u L H : Nat) : (toSteps u (L, H)).1 ≤ (toSteps u (L, H)).2.1 := by
  rw [toSteps_fst, toSteps_snd]; exact Nat.le_max_left _ _

end Formal.Core.XAudit.SoundSteps
