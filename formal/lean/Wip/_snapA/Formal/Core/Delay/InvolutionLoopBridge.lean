import Formal.Core.Delay.InvolutionLoop
import Formal.Cells.ArbInvolution

/-!
# Bridge: InvolutionLoop ↔ CElemInvolution / ArbInvolution

Bridge from A's `InvolutionLoop` to B's `CElemInvolution.orb` / `ArbInvolution`:
the orbits are the same function, and B's critical arbiter gap is A's `crit`.
-/

namespace Formal.Core.InvolutionLoop.Bridge
open Formal.Core.DelayInvolution Formal.Core.InvolutionLoop
open Formal.Cells.CElemInvolution

theorem lo_eq_orb (P : InvolutionPair) (s : ℝ) : ∀ n, lo P s n = orb P s n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [lo_ss, orb_ss, lo_eq_orb P s n, lo_eq_orb P s (n + 1)]

theorem osc_iff (P : InvolutionPair) (s : ℝ) : Osc P s ↔ ∀ n, 0 < wd P s n := by
  constructor
  · intro h n; have := h n; unfold wd; rw [lo_eq_orb, lo_eq_orb]; linarith
  · intro h n; have := h n; unfold wd at this; rw [lo_eq_orb, lo_eq_orb] at this; linarith

/-- B's eternally oscillating arbiter gap is exactly A's critical runt `δ∞↑ - l*`. -/
theorem arb_crit (P : InvolutionPair) {h l s : ℝ} (S : Stat P h l)
    (hs0 : 0 < s) (hsI : s < P.infUp) (hosc : Osc P s) : s = crit P l :=
  crit_unique S hs0 hsI ((osc_iff P s).mp hosc)

end Formal.Core.InvolutionLoop.Bridge
