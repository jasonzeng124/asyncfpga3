import Formal.Core.Substrate
import Formal.Net.Prelim

/-!
# Wip: open statements around the substrate (NOT built, NOT claimed)

Every `sorry` below is an UNPROVED statement. See `formal/notes/A-substrate.md`.
-/

namespace Formal.Core.Substrate.Wip
open Formal.Core.Substrate

/-- (open, ~2 h) 1-D Helly: ℕ delays realised at a REAL corner are realised at
an ℕ (rational) corner. Each arc's scatter constraint is an interval of `c`
with rational ends; finitely many arcs; their intersection is nonempty and
contains a rational point (its left end). Not needed for soundness
(`endpoints_sound_real`, `tight_band_bundle` cover real corners directly);
it would make `CornerModel.Realizes` exactly the real-corner notion. -/
theorem realizes_rational_of_real {A : Type} (M : CornerModel A) (l : List A) (d : A → Nat)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (h : ∀ e ∈ l, Formal.Core.Corner.Scat M.κ.toReal ((M.arc e).toArc.at' c) (d e : ℝ)) :
    ∃ c' : Corner, M.RealizesOn c' d l := by
  sorry

/-- (OPEN QUESTION, not known either way) Is C's `BoundedDelay` closed under
series composition with summed bounds? Its middle signal may hold an old
value while the input chatters (`boundedDelay_not_winR`), which suggests the
composite output can copy a value older than `hi1 + hi2`; a first attempt at
a concrete counterexample did not produce one. `Win` IS closed (`win_comp`),
which is one reason the substrate recommends `Win`. -/
theorem boundedDelay_comp_counterexample :
    ∃ (lo1 hi1 lo2 hi2 : Nat) (i m o : Sig),
      Formal.Net.BoundedDelay lo1 hi1 i m ∧ Formal.Net.BoundedDelay lo2 hi2 m o ∧
      m 0 = i 0 ∧ o 0 = m 0 ∧
      ¬ Formal.Net.BoundedDelay (lo1 + lo2) (hi1 + hi2) i o := by
  sorry

end Formal.Core.Substrate.Wip
