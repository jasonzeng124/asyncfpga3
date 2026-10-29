import Formal.Cells.OnNetlistArbKappaExact
open Formal.Cells.OnNetlistArbKappaExact Formal.Cells.ArbA0Fork
-- MUTANT (must FAIL): 1807/10000 is below the s1c2 cons threshold
example : Below_s1c2_cons k1807 := by decide
-- MUTANT (must FAIL): the fast-corner threshold 82/453 is the exact one (all-safe at 1808/10000 < 82/453)
example : ∀ c d, (∀ e, Scat ⟨1808, 10000, by decide, by decide⟩ c (A_s1c2_cons e) (d e)) → Safe F2 G2 true (dlOf d) := (exact_s1c2_cons _).2 (by decide)
-- MUTANT (must FAIL): s2c2 cons safe at its rational threshold 94/325
example : Below_s2c2_cons ⟨94, 325, by decide, by decide⟩ := by decide
