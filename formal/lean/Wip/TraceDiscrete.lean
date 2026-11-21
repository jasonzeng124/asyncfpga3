import Formal.Core.Trace.Discrete
/-!
# WIP (NOT PROVED, never built): open items for the discrete-time trace probe

Everything here is a statement with `sorry`. Proved material is in
`Formal/Core/Trace/Discrete.lean`. Note: this file imports that module, so it
can only be checked after the lead's `lake build` has built it; the
statements were checked by pasting them at the end of a copy of
Discrete.lean (see formal/notes/A-trace-discrete.md).
-/

namespace Formal.Core.TraceDiscrete.Wip
open Formal.Core.TraceDiscrete

/-! ## W1: event form of the transport channel equals the warp form

Event form: each input transition entering step `u+1` is assigned a delay
`d u ∈ [lo, hi]`; arrivals are non-decreasing in `u` (order preserved, ties
allowed); the output toggles once per arrival (two arrivals on one step
cancel). `arrivals` counts arrivals up to step `t`. -/

/-- Number of input transitions `u < t` whose arrival `u + 1 + d u ≤ t`. -/
def arrivals (i : Sig) (d : Nat → Nat) (t : Nat) : Nat :=
  ((List.range t).filter (fun u => i (u + 1) != i u && decide (u + 1 + d u ≤ t))).length

def EvTransport (lo hi : Nat) (i o : Sig) : Prop :=
  ∃ d : Nat → Nat, (∀ u, lo ≤ d u ∧ d u ≤ hi) ∧
    (∀ u v, u < v → i (u + 1) ≠ i u → i (v + 1) ≠ i v → u + d u ≤ v + d v) ∧
    ∀ t, o t = (i 0 ^^ (arrivals i d t % 2 == 1))

/-- UNPROVED. The two forms agree (sketch in the notes: the warp is
`f t = ` any point between the last arrived transition and the next one). -/
theorem ev_iff_warp (lo hi : Nat) (hlh : lo ≤ hi) (i o : Sig) :
    EvTransport lo hi i o ↔ Transport lo hi i o := by
  sorry

/-! ## W2: a verified decision procedure for the relation on a finite prefix

Greedy: walk `t = 0..H-1`, keep the least feasible `f t ≥ f (t-1)` in
`[t-hi, t-lo]` with `i (f t) = o t`. Least-so-far is optimal (it leaves the
most room), so the greedy succeeds iff some warp exists on the prefix. -/

def greedy (lo hi : Nat) (i o : Sig) : Nat → Option Nat
  | 0 => if i 0 == o 0 then some 0 else none
  | t + 1 =>
    match greedy lo hi i o t with
    | none => none
    | some prev =>
      ((List.range (hi - lo + 1)).map (fun k => t + 1 - hi + k)).find?
        (fun x => decide (prev ≤ x) && decide (x ≤ t + 1 - lo) && (i x == o (t + 1)))

def admits (lo hi : Nat) (i o : Sig) (H : Nat) : Bool :=
  (List.range H).all fun t => (greedy lo hi i o t).isSome

/-- UNPROVED. Soundness and completeness on the prefix `[0, H)`. -/
theorem admits_iff (lo hi H : Nat) (hlh : lo ≤ hi) (i o : Sig) :
    admits lo hi i o H = true ↔
      ∃ f : Nat → Nat, (∀ a b, a ≤ b → b < H → f a ≤ f b) ∧
        (∀ t, t < H → f t ≤ t - lo ∧ t - hi ≤ f t ∧ o t = i (f t)) := by
  sorry

/-! ## W3: discretisation is sound w.r.t. a real-time model (statement only)

Needs track 2's `ℝ → Bool` representation. Claim: if every real delay lies
in `[lo_r, hi_r]` (ps) and the quantum is `q`, the discrete channel
`[⌊lo_r/q⌋, ⌈hi_r/q⌉]` contains the sampling (at multiples of `q`) of every
real-time behaviour whose transitions are at least `q` apart. Not stated in
Lean here: it needs the real-time definitions from the sibling probe. -/

end Formal.Core.TraceDiscrete.Wip
