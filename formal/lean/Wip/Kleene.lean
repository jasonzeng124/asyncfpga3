import Formal.Core.Lut

/-!
# Wip/Kleene — `decide` cost measurements for 6-input Kleene LUT statements

NOT CLAIMED, NOT BUILT. Everything below does check (no `sorry`), but these are
benchmarks, kept out of `Formal/` because some cost over a minute of kernel
time and the general theorems in `Formal.Core.Lut` already cover them.

Measured 2026-10-27 on this sandbox (4 cores, shared), Lean v4.35.0, one file
per statement, wall time including ~1.5 s of Lean start-up; run as
  cd formal/lean && ../slot.sh lake env lean Wip/Kleene.lean
(after Formal.Core.Kleene/Lut oleans exist).

| statement (fixed INIT = bd_c2, 729 = 3^6 Kleene vectors)       | tactic          | wall   |
|------------------------------------------------------------------|-----------------|--------|
| `bench_contain`: X-containment, quantified over all 729 vectors  | `decide +kernel`| 2.5 s  |
| same                                                             | `decide`        | 3.6 s  |
| `bench_mono_step`: one-step monotonicity, 729 × 6 positions      | `decide +kernel`| 21 s   |
| same                                                             | `decide`        | 45 s   |
| `bench_mono_head`: one-step monotonicity at I0 only, 729         | `decide +kernel`| ~7 s   |
| `bench_spec`: mux tree = set spec, 729 × 64 resolutions          | `decide +kernel`| 83 s   |

So: statements quantified over the 729 Kleene inputs of ONE fixed 6-input INIT
are fine for `decide` (seconds), the kernel path (`decide +kernel`, no extra
axioms; it is NOT `native_decide`) is ~2× faster than the elaborator path, and
no `maxRecDepth` was needed for `+kernel` (the elaborator path got
`maxRecDepth 100000` as a precaution). Anything quadratic in the vectors
(e.g. monotonicity as `∀ u v, u ⊑ v → …`, 729² ≈ 5·10⁵ pairs) or quantified
over INITs (2^64) is out of reach and needs the structural lemmas — which are
proved once for all k and all INITs in `Formal.Core.Lut` (`keval_mono`,
`keval_eq_kevalSpec`, `no_static_hazard_single`). Per-cell facts (a handful of
concrete vectors, or ≤ 729 vectors) are best done by `decide`.
-/

namespace Formal.Wip.Kleene
open Formal.Core K3

theorem bench_contain : ∀ v : Fin 6 → K3, v 2 = X → v 3 = zero → v 4 = zero → v 5 = zero →
    (Init.bd_c2.keval v ≠ X ↔ (v 0 = v 1 ∧ v 0 ≠ X)) := by
  decide +kernel

theorem bench_mono_head : ∀ v : Fin 6 → K3,
    Init.bd_c2.keval (vcons X (vtail v)) ⊑ Init.bd_c2.keval v := by
  decide +kernel

theorem bench_mono_step : ∀ v : Fin 6 → K3, ∀ j : Fin 6,
    Init.bd_c2.keval (setAt v j X) ⊑ Init.bd_c2.keval v := by
  decide +kernel

theorem bench_spec : ∀ v : Fin 6 → K3, Init.bd_c2.keval v = Init.bd_c2.kevalSpec v := by
  decide +kernel

end Formal.Wip.Kleene
