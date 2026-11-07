/-!
# Shard C preliminaries: discrete-time traces and bounded delays

Local stand-in until shard A's `Formal/Core/` lands (PROGRAM.md, Shards).
Core Lean only. Same time choice as shard B (`Formal/Cells/Prelim.lean`):
time is `Nat` (one tick = 1 ps), a signal is a `Trace := Nat → Bool`.
LUT semantics (binary and Kleene) live in `Formal.Cells.Prelim`; import that,
do not redefine it, so every proof uses one gate model.

* `Trace`            a binary waveform sampled on integer ps.
* `rises s t`        `s` is 0 at `t` and 1 at `t+1` (an edge between ticks).
* `stableOn s a b`   `s` is constant on `[a, b]`.
* `BoundedDelay lo hi i o`   hypothesis H_BOUNDED_DELAY for one arc: every
  change of `o` copies a value `i` held between `lo` and `hi` ticks earlier,
  and if `i` holds a value for `hi` ticks then `o` takes it. This is a
  relation, not a function: the delay is only known to lie in `[lo, hi]`.
-/

namespace Formal.Net

abbrev Trace := Nat → Bool

def rises (s : Trace) (t : Nat) : Prop := s t = false ∧ s (t + 1) = true
def falls (s : Trace) (t : Nat) : Prop := s t = true ∧ s (t + 1) = false
def changes (s : Trace) (t : Nat) : Prop := s t ≠ s (t + 1)

def stableOn (s : Trace) (a b : Nat) : Prop := ∀ t, a ≤ t → t ≤ b → s t = s a

/-- H_BOUNDED_DELAY (one arc, `lo ≤ hi`):
(1) output changes only to a value the input had some `d ∈ [lo, hi]` ticks earlier;
(2) an input held for `hi + 1` ticks is copied to the output. -/
structure BoundedDelay (lo hi : Nat) (i o : Trace) : Prop where
  cause  : ∀ t, changes o t → ∃ d, lo ≤ d ∧ d ≤ hi ∧ d ≤ t + 1 ∧ o (t + 1) = i (t + 1 - d)
  settle : ∀ t, hi ≤ t → stableOn i (t - hi) t → o t = i t

end Formal.Net
