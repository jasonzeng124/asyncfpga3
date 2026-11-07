import Formal.Net.GcdHwProof

/-!
# Open goal of probe C-8i: the C function is `Nat.gcd` on non-negative i32 inputs

NOT PROVED (this file is Wip; the `sorry` below is the open goal, reported as
such in formal/notes/C-8i-gcdhw.md). Together with the proved
`Formal.Net.GcdHw.Gcd.gcd_hw_graph_computes_gcdC` it would give: for
`a, b < 2^31` every complete run of the imported gcd_hw graph outputs
`Nat.gcd a b`.

Route: show by induction that for `x, y < 2^31` the i32 ops agree with Nat ones
(`shrsi 32 x 1 = x / 2`, `cmpi .slt 32 x 1 = b2n (x = 0)`,
`absd a b = |a - b|`, `minC a b = min a b`, `shli 32 r k = r * 2^k` while
`r * 2^k <= max a b`), so `gcdC (a + b + 64)` follows 8b's `Gcd.gcdC`
step for step, and finish with 8b's `gcdC_eq`. Estimated 1-2 h of core-Lean work.

Below, `#eval` sanity checks (evidence only, not proof).
-/

open Formal.Net.GcdHw.Gcd

theorem gcdC_nonneg31 (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    gcdC (a + b + 64) a b = some (Nat.gcd a b) := by
  sorry

-- evidence: exhaustive on [0, 40)^2, plus a few large values
#eval (List.range 40).all fun a => (List.range 40).all fun b => gcdC (a + b + 64) a b == some (Nat.gcd a b)
#eval [(2147483646, 1073741823), (1836311903, 1134903170), (2147483647, 2147483646), (65536, 1048576)].map
  fun (a, b) => (gcdC (a + b + 64) a b == some (Nat.gcd a b))
-- negative inputs (i32 bit patterns): what the C/hardware returns, for the notes
#eval [((2^32 - 6), 4), (4, (2^32 - 6)), ((2^32 - 1), (2^32 - 1))].map fun (a, b) => gcdC 200 a b
