# A-events9 (probe HDsub): HDsub proved by a first-reach SUB rule (shard A)

STATUS (2026-10-29, probe HDsub, resumed): IN PROGRESS. Plan: (1) compile the dependency
chain into a private overlay (Mathlib-free), (2) move Wip/_snapA Events9{Cert,Beh,Main} to
Formal/Core/XAudit/ and make them check under check.sh, (3) run xevents9 (via `lean --run`
or a compiled binary) on gcd_hw R5 seeds d/3/4/5 x slow/fast/gb/indep, compare with
xevents8 on the same committed bands, (4) negative controls, (5) rerun on E8Mux bands if
notes/A-e8mux.md reports them.

(2026-10-28 text: Lean written, being compiled; rows not yet rerun.)

## Idea (the rule `dsub9`)

A `dsub` judgement (Events8) is a SUB conclusion for a labelled walk that starts at the
guarded source `a = D` instead of the label source `S`. Rule `dsub9` adds one premise:
a log line `wS`, an unlabelled walk `S → a` with at most one token (any delay):
`M v S ≤ M (v − dW) a + tW`, `tW ≤ 1`.

Soundness, by strong induction on time `u` (`Events9Cert.first_reach`): with `m = M u a`
and `s = F xm (u − d1)` the merge sample,
- if `M s S ≤ m`, conservation (`filt_ℓ m + Σ_{i≠ab} filt_i m ≤ m`) and `w1` give
  `filt_ℓ m ≤ P xm ab s + t1` (as the Events7 SUB rule);
- if `M s S ≥ m + 1`, `wS` says `a` had already reached `m` at `u' = s − dW < u`
  (strict because `F xm v < v`); monotonicity gives `M u' a = m`, and the induction
  hypothesis at `u'` plus monotonicity of `P xm ab ∘ F xm` give the bound at `u`.
This is the "first time S reaches 2k+1" argument of A-events8 as a well-founded descent;
the minimum-time witness is the walk `wS`. No parity or timing margin is needed.
