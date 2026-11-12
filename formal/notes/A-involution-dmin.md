# A-involution-dmin: δmin exists; exact input-separation threshold

File: `formal/lean/Formal/Core/Delay/InvolutionDMin.lean` (claimed; passes
`formal/check.sh Formal/Core/Delay/InvolutionTransfer.lean Formal/Core/Delay/InvolutionDMin.lean`
→ `[audit] 222 declarations checked`, `[check] OK`). Declarations are added to the
existing namespace `Formal.Core.DelayInvolution.InvolutionPair` (so `P.dmin` etc. work by
dot notation); existing files are not edited.

## 1. δmin exists (`exists_dmin`, `dmin`, `dmin_spec`)

Assumed: an `InvolutionPair` (its existing fields only). No field is missing, and no
continuity field is needed.
Proved: `∃ d, P.IsDMin d`. `P.dmin` is that value (by choice; it is unique by `IsDMin.unique`,
so `isDMin_iff : IsDMin d ↔ d = dmin`). Also `dmin_pos`, `dmin_lt_infUp`, `dmin_lt_infDown`,
`down_dmin`, `up_dmin`.

Proof route (not IVT): `d = sSup {x | x < δ∞↑ ∧ x < δ↓(-x)}`. `0` is in the set (causality),
and every element is `< δ↑(0)` because `δ↓(-δ↑ 0) = 0 < δ↑ 0` (involution + causality), so
`0 ≤ d ≤ δ↑ 0 < δ∞↑`. If `δ↓(-d) > d` or `< d`, `down_surj` gives an explicit point where
`δ↓` takes a value strictly between `d` and `δ↓(-d)`, and strict monotonicity then yields a
larger element of the set, resp. a smaller upper bound. Surjectivity onto `(-∞, δ∞↓)`
(itself a consequence of the involution property) is what excludes the jump; continuity is
never stated or proved. Only `Mathlib.Algebra.Order.Archimedean.Real.Basic` (the
`ConditionallyCompleteLinearOrder ℝ` instance) is imported additionally; it is built.

`Wip/DelayInvolution.lean`'s `exists_dmin (hcont : Continuous P.down)` (sorry) is subsumed
(the continuity hypothesis is unnecessary); the lead may delete that stub.

## 2. Hypothesis-free corollaries

`cancel_iff'`, `pulse_cancel_iff'`, `pulseWidth_small'`, `transfer_gap'`, `transfer_sep'`,
`sep_threshold_sharp'`: the existing theorems with `IsDMin d` discharged and `d := P.dmin`.
`pulse_threshold_pos`: `0 < δ∞↑ - δmin < δ∞↑` for every pair.

## 3. The asymmetric gap: closed exactly

`S`-separated input: `∀ n, t n + S ≤ t (n+1)`. "Cancels": some `tent (n+1) ≤ tent n`.

`sep_threshold_exact S`: every `S`-separated input is cancellation-free
**iff** `δ∞↑ - δmin < S ∧ δ∞↓ - δmin ≤ S`.

* So the threshold is `max δ∞↑ δ∞↓ - δmin` (the sufficient bound of `transfer_sep` was the
  right number), with a strict inequality on the rising side and a non-strict one on the
  falling side. Reason: the first transition gets exactly `δ∞↑` (input starts low,
  `T = ∞`), every later delay is strictly below its `δ∞` (`tent_sub_lt`).
* Necessity on the falling side (`sep_cancel_down`): for `S < δ∞↓ - δmin`, the witness
  `negPulse L s` (rise at 0, fall at `L`, rise at `L+s`, then every `s`, `s = max S ((δ∞↓-δmin)/2)`,
  `L` large via `down_surj`) cancels transitions 1 and 2. Rising side: `sep_threshold_sharp`.
* `sep_no_cancel` / `sep_no_cancel_tent`: sufficiency. `sep_transfer_exact`: at the exact
  threshold the output is a `Chan δmin (max δ∞↑ δ∞↓)` behaviour (lower band end `δmin`,
  weaker than `transfer_sep`'s band, which needs `S` strictly above `max δ∞ - δmin`).

NOT covered: the full filtered output trace with chained cancellations (unchanged from
`InvolutionTransfer`); "no cancellation" is the `tent` monotonicity event only. The
conventions (input starts low, first transition gets `δ∞↑`) are those of `Involution.lean`;
with input starting high the roles of ↑/↓ swap.

## For the lead

* Root import: add `import Formal.Core.Delay.InvolutionDMin` to `Formal.lean` (the lakefile
  glob already builds it). It imports `InvolutionTransfer`, whose olean was not yet in
  `.lake/build` when checked (check.sh compiled it in the overlay).
* No lakefile change needed.
