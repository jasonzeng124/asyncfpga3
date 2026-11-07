import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! Smoke test for the toolchain: Mathlib imports and a trivial theorem. -/
namespace Formal
theorem smoke : (1 : ℝ) + 1 = 2 := by norm_num
end Formal
