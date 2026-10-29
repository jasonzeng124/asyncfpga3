# A-inv-trace: full trace semantics of the involution channel (probe InvTrace)

STATUS (07:40 UTC): Lean written (Wip/InvTrace/InvolutionTrace.lean, 1000 lines: last
session's draft + the paper's algorithm + list-level theorems + ratPair examples), NOT yet
checked: Mathlib is still building (336 oleans). Will move to
Formal/Core/Delay/InvolutionTrace.lean once check.sh passes.

## The paper's construction (sources)

Web fetch of the papers is blocked in this sandbox (arxiv.org, hal.science do not resolve);
web-search snippets were used:
- M. Függer, R. Najvirt, T. Nowak, U. Schmid, "A Faithful Binary Circuit Model",
  IEEE TCAD 39(10):2784-2797, 2020, doi 10.1109/TCAD.2019.2937748 (HAL hal-02395251;
  repositum.tuwien.at 20.500.12708/140078). Involution channels: delay δ(T) depends on the
  previous-output-to-input offset T; −δ↑(−δ↓(T)) = T; strictly causal pairs have a unique
  δmin > 0 with δ↑(−δmin) = δmin = δ↓(−δmin); bounded SPF unsolvable, unbounded solvable.
- M. Függer, T. Nowak, U. Schmid, "Unfaithful Glitch Propagation in Existing Binary Circuit
  Models", IEEE TC 2016 (ASYNC 2013 version; ieeexplore 7110587). Its *non-forgetful channel
  algorithm*: for each input event (t, x) compute T = t − t' against the previous scheduled
  output t'; if t + δ(T) > t' add (t + δ(T), x) to the output, otherwise remove the pending
  (t', x'). The paper notes an event "is either deleted in the next iteration, or never
  deleted", and that the algorithm may produce events at negative times (T measured from
  a cancelled event). The involution channel is this algorithm with an involution pair.
- Follow-ups (CIDM, Ferdowsi/Maier/Öhlinger/Schmid, arXiv 2104.10966; η-IDM, Függer, Maier,
  Najvirt, Nowak, Schmid, DATE 2018, arXiv 2006.08485): "when out-of-order transitions would
  be scheduled, both are removed"; zero-time glitches are cancelled exactly.

The exact pseudocode was not readable here; the rule above is the snippet's wording.
Two points of the formalization follow it and are stated explicitly in Lean:
1. T is measured from the previous *tentative* output, cancelled or not (`tent`, `step`
   keeps `o' = x + δ(x − o)` as the new reference even when the pair is removed).
2. Cancellation is "not strictly after" (o' ≤ o removes both). The strict/non-strict
   choice only matters at the exact threshold (rat_threshold_cancelled shows the
   boundary case is cancelled).

## Lean design

- Declarative semantics (`outList N t`): transition n is cancelled with n+1 (`CN`) iff
  n+1 < N and tent(n+1) ≤ tent n; survivors (`Surv`) are those cancelled with neither
  neighbour; output = their tentative times in order.
- `cancel_no_chain`: transition n+1 cannot cancel with both n and n+2; so the "remove the
  pending event" step always finds a pending event (`surv_of_cancel`), matching the
  paper's "deleted in the next iteration or never".
- Operational semantics (`step`, `channel : List ℝ → List ℝ`): the paper's algorithm as a
  left fold over the input list. `channel_eq`: equal to `outList` (for any strictly
  increasing extension; `extend` gives one).
