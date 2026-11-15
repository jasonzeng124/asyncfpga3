import Formal.Rewrite.AutoCollatzPreeq2
import Formal.Net.AutoCollatz

/-!
# Formal.Rewrite.Collatz — research's collatz (32-bit) loop-test rewrite: before and after agree (shard A, 2026-11-15)

**Problem, plainly.** Does the handshake graph of `research/data/fifteen/collatz_preeq2.mlir` (loop test `n == 2`)
return what the original graph (`cloud/fixtures/frontend/collatz/comp/handshake_transformed.mlir`, test `n' == 1`)
returns, for every 32-bit input?

**Proved** (`same`): the two cfront transcriptions are the same function (`kC_same`, by `rfl`: cfront read the same C
for both), so on every input on which the C returns `r`, C's `AutoCollatz.auto_computes` (original graph) and
`AutoCollatzPreeq2.auto_computes` (rewritten graph; its rewrite obligations closed by `Eq2.collatz_eq2`) give: both
graphs have complete runs ending with `[r]`, and every complete run of either ends there.

**Not covered:** inputs on which the C never returns (e.g. `n = 0`, negative cycles); gates, delays, cells.
-/

namespace Formal.Rewrite.Collatz
open Formal.Net.Kahn Formal.Net.GcdHw

theorem kC_same : Formal.Rewrite.AutoCollatzPreeq2.kC = Formal.Net.AutoCollatz.kC := rfl

theorem same {fuel n₀ r : Nat} (h : Formal.Net.AutoCollatz.kC fuel n₀ = some r) :
    ((∃ n, Run (step Formal.Net.AutoCollatz.G) (Formal.Net.AutoCollatz.St Formal.Net.CollatzHw.T0 [n₀]) n
        (Formal.Net.AutoCollatz.St Formal.Net.CollatzHw.T1 [r])) ∧
      ∀ m t, Run (step Formal.Net.AutoCollatz.G) (Formal.Net.AutoCollatz.St Formal.Net.CollatzHw.T0 [n₀]) m t →
        Terminal (step Formal.Net.AutoCollatz.G) t → t = Formal.Net.AutoCollatz.St Formal.Net.CollatzHw.T1 [r]) ∧
    ((∃ n, Run (step Formal.Rewrite.AutoCollatzPreeq2.G)
        (Formal.Rewrite.AutoCollatzPreeq2.St Formal.Rewrite.CollatzPreeq2Hw.T0 [n₀]) n
        (Formal.Rewrite.AutoCollatzPreeq2.St Formal.Rewrite.CollatzPreeq2Hw.T1 [r])) ∧
      ∀ m t, Run (step Formal.Rewrite.AutoCollatzPreeq2.G)
        (Formal.Rewrite.AutoCollatzPreeq2.St Formal.Rewrite.CollatzPreeq2Hw.T0 [n₀]) m t →
        Terminal (step Formal.Rewrite.AutoCollatzPreeq2.G) t →
        t = Formal.Rewrite.AutoCollatzPreeq2.St Formal.Rewrite.CollatzPreeq2Hw.T1 [r]) := by
  have h' : Formal.Rewrite.AutoCollatzPreeq2.kC fuel n₀ = some r := by rw [kC_same]; exact h
  exact ⟨⟨(Formal.Net.AutoCollatz.auto_computes h).1, (Formal.Net.AutoCollatz.auto_computes h).2.1⟩,
    ⟨(Formal.Rewrite.AutoCollatzPreeq2.auto_computes h').1, (Formal.Rewrite.AutoCollatzPreeq2.auto_computes h').2.1⟩⟩

end Formal.Rewrite.Collatz
