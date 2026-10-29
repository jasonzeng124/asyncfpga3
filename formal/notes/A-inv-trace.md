# A-inv-trace: full trace semantics of the involution channel (probe InvTrace)

STATUS (08:32 UTC): DONE. `formal/lean/Formal/Core/Delay/InvolutionTrace.lean` checks:

    formal/check.sh Formal/Core/Delay/Pure.lean Formal/Core/Delay/Involution.lean \
      Formal/Core/Delay/InvolutionTransfer.lean Formal/Core/Delay/InvolutionDMin.lean \
      Formal/Core/Delay/InvolutionTrace.lean
    -> [audit] 321 declarations checked / [check] OK

(321 counts all five modules; the deps' oleans were not in .lake/build, so check.sh
compiled them in its overlay.) Unchecked leftover: Wip/InvTrace/ExpReal.lean (the real
exp/log instance; needs Mathlib.Analysis.SpecialFunctions.Log.Basic, not built yet).
Negative controls (scratch, not committed): claiming `ratPair.channel [0, 101/100] = []`
or `ratPair.channel [0, 3/2] = [2, 3]` fails to elaborate, as it must.

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

## What is proved (plain language)

Assumed throughout: one involution channel, i.e. an `InvolutionPair` P (named fields:
δ↑, δ↓ strictly increasing on their domains, bounded by δ∞↑, δ∞↓, the two involution
identities, strict causality). Input initially low; input transition times strictly
increasing. δmin = `P.dmin` (exists by InvolutionDMin, no extra hypothesis).

Semantics (two definitions, proved equal):
- `channel P : List ℝ → List ℝ` -- the paper's algorithm as a left fold (`step`): transition
  k+1 at time x gets candidate o' = x + δ(x − o), with δ = δ↑ for even k+1, δ↓ for odd,
  and o the previous *tentative* output (cancelled or not); the first gets x + δ∞↑. If
  o < o' the candidate is appended, else the last output is removed. o' becomes the new o
  either way.
- `outList P N t` -- declarative: survivors of the pairwise cancellation rule.
- `channel_eq`: on a strictly increasing list, `channel l = outList l.length t` for every
  strictly increasing extension `t` (`extend l` is one).
- `cancel_no_chain` / `surv_of_cancel`: a removal always removes the output of the
  immediately preceding transition, which is still pending (the paper's "deleted in the
  next iteration or never"); no transition takes part in two cancellations.

(a) Agreement with InvolutionTransfer/InvolutionDMin:
- `outList_of_noCancel`: if no cancellation event occurs, the output is exactly
  `tent 0, ..., tent (N−1)` (the objects of the earlier files).
- `channel_of_sep`, `trace_transfer_exact`, `trace_transfer_sep`: S-separated input with
  δ∞↑ − δmin < S and δ∞↓ − δmin ≤ S (the exact threshold of `sep_threshold_exact`): output
  list = tentative times, and the output signal is a `DelayPure.Chan δmin (max δ∞↑ δ∞↓)`
  behaviour of the input; with S > max δ∞ − δmin also the narrower band of transfer_sep.
  `trace_transfer_comp`: then composes with a following bounded pure-delay channel.

(b) Single pulse (`channel_pulse`, `pulse_out`): `channel [a, a+Δ]` (Δ > 0) is `[]` iff
Δ ≤ δ∞↑ − δmin, else `[a + δ∞↑, a + δ∞↑ + Δ']` with Δ' = (Δ − δ∞↑) + δ↓(Δ − δ∞↑)
(`pulseWidth`). `channel_pulse_mono`: above threshold Δ' > 0 and Δ ↦ Δ' strictly
increasing; from earlier files: Δ' < Δ + (δ∞↓ − δ∞↑), and Δ' → 0 as Δ ↓ threshold.

(c) Well-formed output: `channel_sorted` (strictly increasing), `channel_getElem?_dir`
(output transition k comes from an input transition n ≡ k mod 2: alternation, same
direction as its cause), `channel_length_parity` (final output value = final input value),
`channel_mem` (each output s comes from an input n with l[n] + δmin < s < l[n+1] + δmin).

(d) Instances: `ratPair` (δ(T) = 2 − 1/(T+2), δ∞ = 2, δmin = 1), evaluated through the
algorithm with hand-derived values: `rat_runt_cancelled` [0, 1/2] ↦ [];
`rat_threshold_cancelled` [0, 1] ↦ [] (exact threshold, cancelled);
`rat_pulse_shrunk` [0, 3/2] ↦ [2, 17/6] (width 3/2 → 5/6); `rat_memory_channel`
[0, 1/2, 5] ↦ [89/13] (the cancelled runt shortens the next delay to 24/13; a channel that
forgot it would give 7). Exp-channel (abstract exp/log `ExpLog`, δ(T) = T_p +
τ ln(2 − e^{−(T+T_p)/τ})): `exp_channel_pulse`, a pulse is cancelled iff Δ ≤ τ ln 2.
Also `outList_shift_input` (time invariance) and `outList_shiftPair` (involution then pure
delay D ≥ 0 is the involution channel δ'(T) = D + δ(T+D), δ'min = δmin + D).

## What is NOT covered
- Only one channel; no gates, no feedback, no circuit; the paper's bounded-SPF
  impossibility (continuity of circuit traces) is not attempted.
- Continuity of the output in the input times is not stated.
- Inputs must be strictly increasing; simultaneous transitions (zero-time glitches at the
  gate output) are not modelled -- a zero-time gate in front would need that.
- The cancellation comparison is "≤ cancels" (the snippet wording: "out-of-order ...
  removed"); whether the paper cancels on equality could not be read from the paper
  itself (fetch blocked). It only changes the boundary case Δ = δ∞↑ − δmin.
- η-involution channels (adversarial noise) are not covered.
- No link to `TraceEvent.Sig` / other Core trace types; the output signal is a
  `DelayPure.Sig` via `listSig`.
- Real exp/log instance: Wip/InvTrace/ExpReal.lean, unchecked.

## For the lead
- Root import if wanted: `import Formal.Core.Delay.InvolutionTrace` (lakefile glob already
  builds it). Imports Involution, InvolutionTransfer, InvolutionDMin.
- Wip/_snapA/Formal/Core/Delay/InvolutionTrace.lean is superseded (the claimed file extends
  it; the draft did not compile as-is: missing Decidable instance for `Surv`, implicit `P`
  in two calls, `Finset.range_succ` renamed `range_add_one`, two causal proofs, rat_memory).
- `Wip/DelayInvolution.lean`'s `filtered_output_trace` stub (sorry) is superseded by
  `channel`/`channel_eq`.
- Many deprecation warnings (if_pos/if_neg/push_neg) but no errors; same style as the
  existing Involution files.
