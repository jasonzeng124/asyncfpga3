# eq2_check.py controls (shard A, 2026-11-19)

Each mutation makes the rewrite wrong; each must be refused.

| IN | OUT | expected | result |
|---|---|---|---|
| collatz fixture | `collatz_preeq2_lit3.mlir` (research's rewrite with `n == 3`) | refused | REFUSED (planner: OUT's test is not a library identity's right side), rc 2 |
| `collatz_orig_shrui.mlir` (fixture with a logical shift in the step) | research's collatz_preeq2.mlir | refused | REFUSED (planner: the folded test is not the library identity), rc 2 |
| collatz (32-bit) fixture | research's collatz64_preeq2.mlir | refused | REFUSED (normal forms not the same graph, rules_iso), rc 2 |

The same mutations at the Lean level (where a planner bug cannot hide them): `Formal/Rewrite/Steps/Eq2Controls.lean`
(width 2 refused by `ident`; `shrui` refused by `ident`; `n == 3` gives `renCheck = false`).
