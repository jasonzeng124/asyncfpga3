# BDC_FE_EXITCOND as a PASS: what could be proved once, and what cannot (shard A, 2026-11-20)

Status: a design note. Nothing here is proved in general. What is proved is per kernel (FOR-RESEARCH A28:
xorshift, countloop, isprime, horner, `Formal/Rewrite/ExitCond/Auto*EC.lean`).

## The question
Under PROGRAM "General first" (and the auditor's T156), a rewrite that is on for every kernel needs a proof that holds for
every program that matches a pattern. A list of kernels with per-kernel proofs does not count. Can research's
exit-test knob (LLVM indvars, `cloud/fixtures/frontend_exitcond`) be stated as such a pass?

## Two different changes hide under one knob (`tools-A/rewrite/exitcond_opdiff.txt`)
1. **Linear-function test replacement (LFTR): `slt` / `ult` -> `ne` on a unit-step counter.** 35 of 37 kernels.
   countloop's change is typical (fixture lines 6 and 33): the entry guard `cmpi0 = n > 0` is unchanged; the rotated
   loop's test `cmpi1 = (i + 1) < n` becomes `(i + 1) != n`.
2. **A predicate change justified by "no signed overflow" (nsw).** This happens on gcd only: `cmpi12` `slt -> ult`.
   This is NOT a graph equivalence. The two graphs differ on (2147483647, -1) (A28, `exitcond_gcd_ce.py`), so no pass
   can contain it. It can only be justified against the C, and only on inputs where the C has no UB.

## Change 1 is a true graph equivalence, under side conditions that can be checked on the MLIR
No UB argument is needed. Suppose:
- (a) the compared value is a ring counter `i` plus the constant 1, or the counter itself;
- (b) the counter starts at `s` and every trip adds exactly 1;
- (c) the bound `n` is loop-invariant: it is carried round the ring unchanged, or it is a constant;
- (d) the loop runs only if the entry guard holds: `s < n` for the same signedness, and the zero-trip path is routed
  around the loop.

Then the counter satisfies `s <= i < n` on every trip. So `i + 1 <= n`, and `i + 1 < n` iff `i + 1 != n`. No value
wraps: `i + 1 <= n <= INT_MAX`, or `UINT_MAX` in the unsigned case.

This argument covers every input, n <= 0 included, because (d) diverts those inputs before the test is ever evaluated.

## Why the Lean does not have it yet
The step from `<` to `!=` needs the invariant `i < n` on the ring's reachable states. That is a RELATION between the
k-th tokens of two ring channels, the counter and the carried bound. Formal's current tools cannot express it:
- the local-step scripts (`Rewrite/Steps`) need equalities that hold on every token;
- `ChanInv` gives a per-channel (unary) invariant;
- `PairInv` pairs one channel with itself;
- the per-kernel autoproof's state correspondence must hold on every C state, not only the reachable ones. This is
  why nested fails: `j != b` equals `j < b` only when j <= b.

What the general theorem would need:
- a two-channel ring invariant, proved inductively over the ring's firing rule (initial tokens from (d); preserved
  by +1 and the test's true branch);
- a congruence step that swaps a compare under that invariant.

The previous estimate stands: days, not hours. A Bool checker for (a)-(d) on the MLIR is the easy part.

## Recommendation to research (also in FOR-RESEARCH A28)
- If exit1 shows a gain, gate the knob kernel by kernel: keep LFTR, and keep gcd's nsw predicate change out.
- Until the general theorem exists, the per-kernel proofs (about a minute each to regenerate) are the ticket for
  LFTR. The nsw change has no ticket.
