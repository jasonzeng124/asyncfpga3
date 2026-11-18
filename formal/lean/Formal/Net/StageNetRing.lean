import Formal.Net.StageNet
import Formal.Net.Ring

/-!
# The stage rule is the `bd_link` controller's LUT (shard C, 2026-11-18)

**Problem, plainly.** `StageNet` models a storage stage as "excited when every stage feeding it
differs and every stage it feeds equals it". For a stage with one predecessor `a` and one
successor `b` (a stage inside a `bd_link` chain or a `bd_pipe`), this file shows that rule is
exactly the real controller: `bd_c2n` with `rst = 0`, i.e. `c = C(a, ¬b)`, is excited (its LUT
output differs from its state) iff the stage rule says so. `Ring.c2n_run` / `c2nset_run` tie
`Ring.ctl` to the verbatim LUT INITs of `cells/rtl/bd_ce.v` (shard B's `CElemFn`).

Not covered: stages with several predecessors or successors (a C-element join or fork in
between: H_RENDEZVOUS).
-/

namespace Formal.Net.StageNet
open Formal.Cells.CElemFn

theorem excited_single {V : Type} (E : V → V → Prop) (x : State V) {t a b : V}
    (hp : ∀ p, E p t ↔ p = a) (hs : ∀ q, E t q ↔ q = b) :
    Excited E x t ↔ c2nB (x a) (x b) (x t) false ≠ x t := by
  rw [Ring.c2n_run, Ring.ctl_ne_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1 a ((hp a).2 rfl), h2 b ((hs b).2 rfl)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hpt => ((hp p).1 hpt) ▸ h1, fun q hq => ((hs q).1 hq) ▸ h2⟩

/-- The same for the `_set` variant (comes up 1 at reset). -/
theorem excited_single_set {V : Type} (E : V → V → Prop) (x : State V) {t a b : V}
    (hp : ∀ p, E p t ↔ p = a) (hs : ∀ q, E t q ↔ q = b) :
    Excited E x t ↔ c2nsetB (x a) (x b) (x t) false ≠ x t := by
  rw [Ring.c2nset_run, ← Ring.c2n_run]
  exact excited_single E x hp hs

end Formal.Net.StageNet
