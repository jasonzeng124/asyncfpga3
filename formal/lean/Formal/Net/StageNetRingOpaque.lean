import Formal.Net.StageNetRingLive

/-! # A live ring is never open all the way round (shard C, 2026-11-22)

**Problem, plainly.** In the event storms formal's simulator found under inflated delay scatter (FOR-RESEARCH
C79), the data latches all the way round a loop ring were transparent at once, so the loop's data closed a
combinational path through the adder. Can that happen when the handshakes keep their order (speed
independence), or does it need a timing failure?

In the stage model (`StageNet`, Muller half-buffer stages round a ring of `n + 1` stages), a *boundary* is a
neighbouring pair whose states differ: stage `i` holds a token that `nxt i` has not taken yet. In a bd link, that
is the moment its latch holds its captured value (closed) because the next stage has not acknowledged it.

**Proved here.**
* `boundary_always`: if the ring starts trap-free (`0 < D x < n + 1`, e.g. research's floor
  `1 ≤ T`, `S ≥ 2T + 1`), then in EVERY state reachable by firing there is a boundary. Also some pair agrees.
* `boundary_count_pos`: the same as `0 < D y`.

**What it does not cover.**
* That a boundary means a closed latch is the cell semantics of the bd link. It is not derived here.
* Timing: the theorem is about the order of handshakes only. It says that a cut-free (all-open) ring needs the gates
  to leave the stage model, i.e. a timing failure such as a latch closing after its data has already gone round,
  or a control glitch. It does not say which.
-/

namespace Formal.Net.StageNet.RingLive
open Formal.Net.StageNet

variable {n : Nat}

/-- **In every reachable state of a ring that starts trap-free, some stage differs from the next one (a
token not yet taken), and some stage agrees with the next one (a bubble).** -/
theorem boundary_always {x y : State (Fin (n + 1))} (h0 : ¬ HasTrap E x) (hr : Reach E x y) :
    (∃ i, y i ≠ y (nxt i)) ∧ (∃ j, y j = y (nxt j)) := by
  have hy : ¬ HasTrap E y := fun h => h0 ((trap_reach_iff E hr).mpr h)
  obtain ⟨hagree, hdiff⟩ := (ring_noTrap_iff y).mp hy
  exact ⟨hdiff, hagree⟩

/-- The same, as a count: the number of boundaries stays positive (and below the ring's size). -/
theorem boundary_count_pos {x y : State (Fin (n + 1))} (h0 : ¬ HasTrap E x) (hr : Reach E x y) :
    0 < D y ∧ D y < n + 1 := by
  have hy : ¬ HasTrap E y := fun h => h0 ((trap_reach_iff E hr).mpr h)
  exact (ring_noTrap_iff_count y).mp hy

/-- Research's floor gives the premise: a ring of `S = n + 1` stages with `T ≥ 1` tokens and `S ≥ 2T + 1`,
at its rest marking (`D x = 2 T`), has a boundary in every reachable state. -/
theorem boundary_always_floor {x y : State (Fin (n + 1))} (T : Nat) (hT : D x = 2 * T)
    (h1 : 1 ≤ T) (hS : 2 * T + 1 ≤ n + 1) (hr : Reach E x y) : ∃ i, y i ≠ y (nxt i) :=
  (boundary_always ((ring_live_tokens x T hT).mpr ⟨h1, hS⟩) hr).1

end Formal.Net.StageNet.RingLive
