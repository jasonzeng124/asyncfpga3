# B probe 5e: the `bd_c2` loop under shard A's involution channel

File: `formal/lean/Formal/Cells/CElemInvolution.lean` (about 1280 lines;
imports `Formal.Cells.CElemTiming` (for `exc`, `INIT_c2`, `c2_eq`), shard A's
`Formal.Core.Delay.Involution`, and Mathlib `Algebra.Order.Archimedean.Real.Basic`,
`Topology.Order.MonotoneContinuity`, `Topology.Order.Compact`,
`Topology.MetricSpace.Pseudo.Lemmas`, `Topology.Algebra.Ring.Real`).
It does NOT import 5d's `CElemCore` (that file has no olean in `.lake/build`); the
pieces of 5d it needs are re-proved here on A's channel.

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH ../slot.sh lake env lean Formal/Cells/CElemInvolution.lean

Status: **checks clean** (0 errors, 0 warnings, about 13 s). No
`sorry`/`admit`/`axiom`/`native_decide`. `#print axioms` on `c2_eternal`,
`c2_slow_resolution`, `loop_orb`, `loop_exists`, `crit_exists`, `inv_eternal`,
`den_inj`, `up_not_continuous`, `window_lower` and `sym_const_gap` shows only
`propext`, `Classical.choice` and `Quot.sound`.

## 0. What A provides, and two discrepancies with 5d

A's `Involution.lean` has `InvolutionPair` (domains, strict monotonicity,
involution law, causality) and the transition semantics `tent`: the tentative
output of input transition `n` is `t n + δ(t n - tent (n-1))`, and out-of-order
tentative outputs annihilate (`cancel_iff`). **A has no signal-level relation
on `ℝ → Bool`.** The full trace semantics, with chained cancellations, is A's
open Wip item `filtered_output_trace`. So goal (1) needed a signal-level
relation, and I built one on A's `tent` (section 2 below).

* `up_contAt`, `down_contAt`: A's delay functions are continuous on their
  domains. This is DERIVED from A's fields: a strictly monotone function whose
  image is an interval (A's `up_surj`) is continuous
  (`StrictMonoOn.continuousAt_of_image_mem_nhds`). No continuity hypothesis is
  added.
* **Discrepancy 1** (`up_not_continuous`): no A pair has a `δ↑` that is
  continuous on all of `ℝ`, because `δ↑` is unbounded below on
  `(-δ∞↓, 0)`. 5d's `InvCh` assumes `Continuous dU` and the involution law for
  every `T`, and its `dUinf` is a free number, not tied to the delay
  functions. So 5d's `InvCh` is a different channel class. `inv_eternal` does
  not transfer by instantiation, and I re-proved it while tracking domains:
  `dom_chain` shows that every delay argument along a non-cancelling prefix
  stays in its domain.
* **The recurrence itself agrees exactly.** 5d's `orb` (with `dU = δ↑`,
  `dD = δ↓`, `dUinf = δ∞↑`) is what the signal-level loop produces
  (`loop_orb`, `tent_eq_orb`). Ties cancel in both, since A's `cancel_iff`
  uses `≤`.
* **Discrepancy 2 (small):** 5d's right endpoint `Δ0 = δ∞↑` is not a legal
  input for the signal-level relation. There, `b` falls exactly when `qp`
  rises, so the input sequence is not strictly increasing. I replaced it with
  an interior latching width `r < δ∞↑` (`right_in_H`), using continuity at
  `δ∞↑`.

## 1. Orbit level (on A's `InvolutionPair`)

* `orb P Δ0`: `o0 = δ∞↑`, `o1 = Δ0 + δ↓(Δ0 - δ∞↑)`,
  `o(n+2) = o n + δ_n(o n - o(n+1))` (`δ_n = δ↑` for even `n`).
* `isOpen_L`, `isOpen_H`: the LOST set (first cancellation at an even index)
  and the LATCHED set (odd index) are open. This uses continuity at
  points only, and the extra open condition `Dom (n+1)` in the tie sets `W n`.
* `LH_disjoint`, `cover`: the two sets are disjoint and cover every
  non-oscillating width in `(0, δ∞↑)`. A tie is resolved two transitions
  later by the involution law at `T = 0` (`dA_inv`).
* `lft_in_L`: `l = δ∞↑ - δ↑(0)` is lost. `right_in_H`: some `r ∈ (l, δ∞↑)`
  latches.
* **`crit_exists`**: there is a critical width `c ∈ (l, δ∞↑)` that oscillates
  forever (`Osc`), and LOST widths accumulate at `c` from the left. `c` is
  the supremum of the lost interval that starts at `l`. This proves 5d's
  connectedness result and also says where the critical width sits.
  `inv_eternal` is the existence part alone.
* `osc_unbounded`: no Zeno behaviour. On an oscillating orbit
  `o(2k) ≥ o0 + k·p` with `p > 0`.

## 2. Signal level: the loop, and the derivation of `orb`

* `den s ok`: the signal that starts at 0 and toggles at the active times
  `s n`. `den_inj` shows that transition times are determined by the signal:
  two increasing sequences that denote the same signal agree.
* `InvRun P t ok okO` / **`InvChanF P x y`**: the signal-level channel
  relation. `x = den t ok`, `y = den (P.tent t) okO`, and the run has one of
  three shapes:
  1. infinitely many inputs and no cancellation;
  2. inputs `0..m+1`, where tentative outputs `m` and `m+1` annihilate
     (`tent (m+1) ≤ tent m`, A's rule) and outputs `0..m-1` survive;
  3. finitely many inputs and no cancellation.

  **This is a fragment of the paper's semantics: at most one cancellation,
  and only of the last two tentative transitions.** Input sequences with
  interior cancellations have no output under `InvChanF`.
* **`CLoop P Δ0 a b rst x qp`**, the loop structure. Its named hypotheses:
  * `H_A`, `H_RST`: `a = 1` and `rst = 0`;
  * `H_RUNT`: `b = [0, Δ0)` at the pin;
  * `H_LUT`: `x = exc INIT_c2 (a, b, qp, rst)`, i.e. the REAL INIT through
    `lutB`, applied in zero time (Függer's gate model);
  * `H_CH : InvChanF P x qp`: ONE involution channel, with the LUT and the
    feedback wire lumped.
* **`loop_orb` (the derivation; goal 1)**: for `0 < Δ0 < δ∞↑`, in EVERY
  solution the output is either
  * `qp = den (orb P Δ0) all` and `Osc` holds, or
  * `qp = den (orb P Δ0) (· < m)`, where `m` is the first index with
    `o(m+1) ≤ o m`. The output is then constant after `o(m-1)`: 0 if `m` is
    even (LOST), 1 if `m` is odd (LATCHED).

  The proof goes as follows.
  * The first input transition is at 0 (by causality: `tent 0 = t0 + δ∞↑`).
  * The input `b ∨ qp` is then the signal of the sequence
    `0, Δ0, tent 0, tent 1, …` (`den_cons2`).
  * By `den_inj`, `t (n+2) = tent t n`: the feedback closes the loop.
  * Then `tent t = orb` (`tent_eq_orb`).
  * Shape 3 is impossible, because the loop always has two more inputs than
    surviving outputs.

  **5d's recurrence is therefore derived, not assumed.**
* **`loop_exists`**: for every `0 < Δ0 < δ∞↑` a solution exists: the input
  sequence is `cons2 0 Δ0 (orb …)`, and its tentative outputs are `orb`
  (`tent_cons2`). So `loop_orb` is not vacuous, and inside the fragment the
  loop is deterministic.
* **`c2_eternal` (goal 2)**: some `Δ0 ∈ (δ∞↑ - δ↑(0), δ∞↑)` has a solution,
  and in EVERY solution `qp` takes both values after every time bound `B`.
* **`c2_slow_resolution` (goal 3)**: let `c` be the critical width. For every
  `ε > 0` and every `B` there is `Δ0 ∈ (c - ε, c)` that has a solution, and
  every solution for that `Δ0` behaves the same way:
  * it is LOST: `qp` is eventually constant 0;
  * yet `qp = 1` at some time after `B`.

  So the resolution time is unbounded on every neighbourhood of `c`. This is
  the involution model's metastability, with no analog state.

On the full semantics: inside the loop, the input changes only when an
output transition occurs. After the first cancellation no output is pending,
so no further input comes. Every run of the loop under the full semantics is
therefore one of the fragment's shapes. This argument is informal; proving it
needs A's full trace semantics.

## 3. Quantitative bound, and comparison with 7d's `e^{-t/τ}`

* `QuantHyp P c K M g`, with named fields:
  * `H_LIP`: `|δ_n a - δ_n b| ≤ K|a - b|` on `[-M, ∞)`. This is only
    possible away from the domain edge, where `δ → -∞`. Test: the slope of the
    measured pulse-shrink curve of LUT + route.
  * `H_MARGIN`: every gap of the critical orbit is `≥ g`.
  * `H_GAPMAX`: every gap of the critical orbit is `≤ M - g`.
  * `H_FIRST`: `c - δ∞↑ ≥ -M`.
* **`window_lower`**: if `2 (1+2K)^N (1+K) |Δ0 - c| < g`, then `Δ0` has no
  cancellation among its first `N+2` output transitions, and the `N`-th
  transition happens after `δ∞↑ + N g - g/2`.
* **What this means.** Write `T ≈ N g` and `τ_inv = g / ln(1+2K)`. The runt
  widths that are still switching at time `T` include an interval of
  half-width `≥ g/(2(1+K)) · e^{-(T-δ∞↑)/τ_inv}`. A runt-width density `p`
  turns this into `P(unresolved at T) ≥ const · p · e^{-T/τ_inv}`.
* **Comparison with 7d.** 7d proves the analog bound
  `P(unresolved at T) ≤ 2pδ e^{-T/τ_r}`. The shape is the same, and here it is
  a LOWER bound from the binary model. Proving the matching upper bound needs
  a hyperbolic (expanding) critical orbit, i.e. derivative or concavity
  information, which A does not assume.
  * Heuristic only: for a symmetric channel the gaps follow the 1-D map
    `F(w) = -w + δ(-w)`. At its fixed point `w*` (`δ(-w*) = 2w*`) the
    multiplier is `-(1 + δ'(-w*))`, which suggests
    `τ_inv ≈ w* / ln(1 + δ'(-w*))`. This parallels 7d's `τ_r = τ/(g-1)`.
* `sym_const_gap` partly answers whether the hypotheses can hold: for a
  symmetric channel, an orbit whose first gap is a fixed point `w` keeps
  every gap equal to `w`. It oscillates forever and satisfies
  `H_MARGIN`/`H_GAPMAX` with `g = w` and `M = 2w`. The existence of `w`, and
  of a `Δ0` with that first gap, needs the IVT and is not proved.

## Not proved / gaps

* The full involution trace semantics (A's Wip item) is not done, so the
  claim that the fragment covers all runs of the loop is argued only in prose.
* Uniqueness of the critical width, and the matching exponential UPPER
  bound on the unresolved window. Both need concavity or derivative bounds.
* The consistency of `QuantHyp` for the actual critical `c` of
  `crit_exists` (only the symmetric constant-gap orbit is exhibited, and its
  existence is not proved).
* No probability measure: the `e^{-T/τ}` statement is about interval widths.
  Multiplying by a density bound, as 7d does, would be routine.
* `η`-involution channels (adversarial noise) are not attempted.

## Verdict

**Works.** All three goals are proved in about 2.5 h, plus a quantitative
lower bound. Two hidden assumptions of 5d turned out to need replacing:
`InvCh`'s global continuity and global involution law are incompatible with
A's channel (`up_not_continuous`). Shard A has no signal-level relation, so
this probe supplies a fragment relation (`InvChanF`) on A's `tent`.

Effort to finish:
* the full trace semantics and a proof that the loop's runs lie in the
  fragment: 1–2 days, which is shared with A's Wip item;
* the hyperbolicity-based upper bound: about 1 day once concavity is added
  to A's pair.

What it buys the project: a gate-level metastability theorem for the
feedback-LUT C-element on shard A's channel. The theorem uses the cell's real
INIT and derives the transition recurrence from the signal level. It shows
three things:
* there is a runt width that never resolves;
* nearby widths resolve arbitrarily late;
* the window of late widths is at least exponentially thin in time, which is
  7d's law seen from the binary side.

So no timing checker may rely on runts dying out, and the `Dmax` minimum pulse
width (5b/5d) must be ENFORCED.

## Fidelity per primitive

* **LUT**: the Boolean function comes from the REAL INIT `0x00E8…` through
  `lutB` (`exc`, with `exc_or` proved from `c2_eq`). It is applied in ZERO
  time. All delay and pulse shaping of the mux tree (input buffer,
  pass-transistor tree, output buffer) is moved into the channel. There is no
  `X` and no intermediate level.
* **Feedback wire**: lumped with the LUT into one involution channel. That a
  LUT channel and a wire channel in series equal one involution channel is
  NOT proved here, and I do not know that it holds in general (I could not
  check the papers on whether involution channels are closed under series
  composition).
* **Channel**: A's `InvolutionPair`. Its fidelity is as in A's notes: it is
  validated against SPICE for inverter chains. For a LUT it must be fitted per
  (pin, edge). Test: inject runts of controlled width through LUT + route,
  measure the surviving width (TDC), and fit `Δ ↦ Δ'`. The model predicts a
  strictly increasing map that is continuous down to 0. The same data gives
  `K`, the slope used in `H_LIP`.
* **Inputs**: `a`, `rst` constant and `b` an ideal runt at the pin. Input
  routing belongs to the driver.
