# A / track 3c: involution channel, transfer to bounded pure delay

Probe InvTransfer. It answers the audit's OVERSTATED verdict on the
"transfer lemma" (`git show origin/claude/audit:audit/findings/A.md`, the
`up_bounds` row). Before this probe, Lean proved only that the delay function is
monotone and bounded (`up_bounds` and `down_bounds` in `Involution.lean`). That
statement used `T`, the time since the previous output. Nothing related it to
`DelayPure.Chan`, nothing stated "no cancellation", and no `InvolutionPair`
instance existed in the claimed build.

File: `formal/lean/Formal/Core/Delay/InvolutionTransfer.lean`, namespace
`Formal.Core.DelayInvolutionTransfer`. `Involution.lean` is unchanged.

## What is proved

The notation below is `D = max δ∞↑ δ∞↓`. `d` is δmin, given by the hypothesis
`IsDMin d`.

1. **Non-vacuity.** `ratPair` is a concrete `InvolutionPair` with
   `δ↑ = δ↓ = δ(T) = 2 − 1/(T+2)` on `T > −2` and `δ∞ = 2`. `rat_dmin` proves
   δmin = 1. The involution property holds exactly (`rat_inv`): `−δ(T) + 2 = 1/(T+2)`, so
   `δ(−δ T) = 2 − (T+2) = −T`. The exp-channel is not used, because
   `Real.exp` and `Real.log` are not available in the built Mathlib subset
   (`Wip/DelayInvolution.lean`).
2. **Bridge** (`chan_sigOf`). `sigOf N u` is the signal that starts `false` and
   toggles at `u 0 … u (N−1)`. Assume:
   - input times `t` are strictly increasing;
   - output times `o` are monotone, so no two outputs are reordered;
   - `lo ≤ o n − t n ≤ hi` for every `n`.

   Then `Chan lo hi (sigOf N t) (sigOf N o)` holds for every `N`. The proof uses
   an explicit read map `σ s = max (s − hi) (t (k−1))`, where `k` is the number of
   output events at or before `s`.
3. **`transfer_gap`, output-relative form.** Assume `∀ n, T0 ≤ t(n+1) − tent n`
   with `T0 > −δmin`. Then:
   - (i) `tent` is strictly increasing. So there is no cancellation, and each input
     transition gives exactly one output transition, at `tent n`.
   - (ii) every delay lies in `[min(δ↑T0, δ↓T0), D]`.
   - (iii) `Chan` with that band relates `sigOf N t` and `sigOf N (tent t)`.
4. **`transfer_sep`, input-separation form.** Assume `∀ n, t n + S ≤ t(n+1)` with
   `S > D − δmin`. Then (i) to (iii) hold with `T0 = S − D`.
   `band_lo_gt_dmin` shows that the lower end of the band is greater than δmin,
   which is greater than 0.
5. **Sharpness and negative controls.**
   - `sep_threshold_sharp`: take any involution pair and any `0 < S ≤ δ∞↑ − δmin`.
     The `S`-spaced input `t n = n·S` cancels its first pulse
     (`tent 1 ≤ tent 0`).
   - For symmetric pairs (`δ∞↑ = δ∞↓`), the threshold `S > δ∞ − δmin` is therefore
     exact.
   - On `ratPair` with `S = 1 = δ∞ − δmin`, both tentative outputs fall at time 2
     and annihilate (`rat_cancel_at_threshold`, `rat_threshold_values`).
     `rat_cancel_half` is the same check at `S = 1/2`.
   - Positive example (`rat_transfer_example`): with `S = 3/2` the channel is
     `Chan (4/3) 2`.

## Which separation notion, and why

The paper's variable is `T = t(n+1) − o(n)`, the time from the previous
(tentative) output to the current input. A hypothesis on `T` mentions the
channel's own output, so it suits closed-loop proofs, such as a handshake where
the environment reacts to the output. That is `transfer_gap`.

An environment specification usually states only input separation. The link
between the two is `T(n+1) ≥ S − δ∞(n)`, which holds because `tent n ≤ t n + δ∞`
(`tent_le`). This gives `transfer_sep` with `T0' = S − D`. The cost is that the
threshold rises from `T0 > −δmin` to `S > D − δmin`.

The audit's reading of the old claim ("input separation T0, band `[δ(T0), δ∞)`")
was wrong in two places:
- The band argument is `S − D`, not `S`.
- The top of the band is closed. The first transition gets exactly `δ∞↑`, by the
  `T = ∞` convention. Every later delay is strictly below δ∞.

The input-separation threshold is also not `T0 > −δmin`. It is `S > D − δmin`, and
that is sharp for symmetric channels.

## What is NOT covered

- **Asymmetric channels.** The gap between the necessary bound
  `S > δ∞↑ − δmin` and the sufficient bound `S > max(δ∞↑, δ∞↓) − δmin` is not
  resolved. Per-direction bounds would be sharper. One example: a rising
  transition after a falling one needs `S − δ∞↓ > −δmin`. This is not done.
- **Filtered output trace.** The general output trace with chained cancellations
  is not formalized. The theorems cover only the no-cancellation regime, where the
  output *is* `tent 0, tent 1, …` by the paper's rule. The negative controls show
  that `cancel_iff`'s condition fires. They do not compute the filtered trace.
- **Initial value and trace length.** The initial value is `false` (the input
  starts low). Hypotheses are stated on an infinite sequence `t : ℕ → ℝ`. A finite
  trace of N transitions is covered by extending it with S-spaced dummy
  transitions, which leave `tent 0 … tent (N−1)` unchanged. That extension step
  is argued here in prose; it is not a Lean lemma.
- **Existence of δmin.** It is still a hypothesis, `IsDMin`. For `ratPair` it is
  proved.
- **Use in cell proofs.** A cell proof that uses `Chan` for every input must
  discharge the S-separation obligation on that channel's input. This is a
  per-cell environment or closed-loop lemma.

## Requests for the lead

- No lakefile change is needed, because the `Formal.+` glob picks the file up.
- Optional root import in `Formal.lean`: `import Formal.Core.Delay.InvolutionTransfer`.
  It imports `Involution` and `Pure`, so `Involution` stops being an orphan.
- FEASIBILITY track 3 wording: replace the "transfer lemma" sentence with the
  statement of `transfer_sep` given above.
