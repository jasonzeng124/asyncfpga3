import Formal.Core.XAudit.Untimed
import Formal.Core.XAudit.Fast

/-!
# Wip/XAudit — open statements of probe A-xaudit (NOT built, NOT claimed)

Everything here is UNPROVED (`sorry`, clearly marked). See
`formal/notes/A-xaudit.md`, section "What is not proved".
-/

namespace Formal.Core.XAudit.Wip

open Formal.Core.Ternary
open Formal.Core.Ternary.K3

/-! ## W1. Chaining the untimed phases

`xaudit` runs the untimed A/B phase by phase and starts phase `i+1` from the B
row of phase `i`. `Untimed.untimed_noGlitch`/`untimed_settles` are proved per
phase, with the hypothesis that the phase's start state is covered by its
start row. Discharging that hypothesis for phase `i+1` from `settleB0` of
phase `i` needs a semantics that can restart: the `Causal` relation lets a
node sample ANY earlier time, so a late phase may still see samples from
before the previous transition. The intended statement assumes bounded
staleness `D` throughout and phases at least `(n+1)·D` apart (fundamental
mode), and covers every time of every phase. -/

/-- UNPROVED. Phases `0..k` with input vectors `vs i`, starting at times
`T i` (increasing, gaps `≥ (n+1)·D`), inputs equal to `vs i` on
`[T i, T (i+1))`; the rows `r i` are the executable's chain
(`r 0 = rowX`, `r (i+1) = runB … (vs i) (vs (i+1)) (r i)`). Then every state
from `T i + n·D` to `T (i+1)` is covered by `r (i+1)`. -/
theorem chain_phases {n : Nat} (N : Net (Fin n) (Fin n)) (D : Nat) (k : Nat)
    (vs : Nat → Fin n → Bool) (T : Nat → Nat) (r : Nat → Array Formal.Core.Ternary.K3)
    (hr0 : r 0 = Untimed.rowX n)
    (hr : ∀ i, r (i + 1) = Untimed.runB N (vs i) (vs (i + 1)) (r i))
    (hT : ∀ i, T i + (n + 1) * D ≤ T (i + 1))
    (c : Nat → Fin n → Bool) (σ : Nat → Fin n → Bool)
    (hc : ∀ i t, T i ≤ t → t < T (i + 1) → c t = vs i)
    (hD : Stale N c σ D) :
    ∀ i, i ≤ k → ∀ t, T i + n * D ≤ t → t < T (i + 1) →
      VLe (Untimed.rget (r (i + 1))) (vb (σ t)) := by
  sorry -- W1: open (about 0.5 day: a "covered window" variant of sound_postfix under Stale)

/-! ## W2. Transport (FIFO) precision

`XSim.sound` is proved for the non-FIFO window channel `WinCh`, which allows a
wire to show a train of old and new samples inside its window. That is why a
free-running ring (`results/ring3_slow_corner.txt`) loses its phase after one
lap although every fixed-delay transport run is clean (scratch Python check,
200 random delay assignments). A sharper abstract domain for monotone warps
would track, per wire, "one transition inside [t1, t2]" instead of "X on
[t1, t2]". Statement to aim for (shape only): -/

/-- UNPROVED, shape only: a FIFO-aware simulator `histT` whose rows refine
`XSim.val` and remain sound for `Transport` circuits. -/
theorem fifo_refines_placeholder : True := by
  sorry -- W2: open (design of the domain is the work; 2-4 days)

end Formal.Core.XAudit.Wip
