# A-ternary-channels: ternary simulation is sound for the Core/Delay transport and inertial channels

Probe TernSound (shard A). File: `formal/lean/Formal/Core/TernaryChannels.lean`
(namespace `Formal.Core.TernaryChannels`).

Audit row being closed (`audit/findings/A.md`, Ternary.lean header / FEASIBILITY §4):
"only `gmw_causal` (GMW ⊆ Causal) is proved; transport and inertial are covered
in prose". Verdict of this probe: **the prose claim was not literally true, and it
is now proved in the form below**.

## How to check

```
formal/check.sh Formal/Core/TernaryChannels.lean
```
Result: see "Check result" at the end.

## The finding: a type mismatch, and a missing hypothesis

1. `Ternary.Causal` is a predicate on **discrete** behaviours (`ℕ → ν → Bool`).
   `DelayPure.Chan`, `DelayInertial.InertialRD` and `BoundedInertial` relate
   **continuous** signals (`ℝ → Bool`). So "transport/inertial ⊆ Causal" has no
   literal meaning; it needs a choice of discrete time, and the naive choice
   (sampling on a grid) is **false** in general: `sample_not_causal`.
2. Even in continuous time, soundness needs **a positive lower delay bound**.
   With `lo = 0` (transport) or `Δ = 0` (inertial) a buffer fed back to itself
   may switch spontaneously although algorithm A says it holds:
   `zero_delay_chan_unsound`, `zero_delay_inertial_unsound`. The prose
   "every causal delay behaviour" hid this: the discrete `Causal` builds it in
   (a sample is taken at a step `≤ t` for the value at `t+1`, i.e. a delay of at
   least one step).
3. For settling, the prose said inertial channels do not satisfy `Stale` (true)
   and left "inertial → settling" as W4. **It is now proved**, through a weaker
   hypothesis `SettlesWithin D` that both channel kinds satisfy.

## What is proved (exact names)

Definitions.
- `ReadsPast δ x y`: every output value is an input value from at least `δ` earlier.
- `SettlesWithin D x y`: if `x = v` on `[T, ∞)` then `y = v` on `[T + D, ∞)`.
- `NodeChan δ D x y`: `y` is `Chan lo hi x` or `BoundedInertial ρ lo hi x`, with
  `δ ≤ lo`, `hi ≤ D` (per node, so mixtures are allowed).
- `exc N c σ i` = `fun s => N.fb (c s) (σ s) i` (zero-delay gate excitation);
  `node σ i` its output waveform.
- `RCausal N c σ δ`: continuous-time analogue of `Causal`: for `s ≥ 0` each node
  value is `N.fb` of input/node samples each taken at a time `≤ s − δ`
  (per-wire sample times allowed).

Channel facts.
- `chan_readsPast` (`Chan lo hi ⊆ ReadsPast lo`), `chan_settles` (`⊆ SettlesWithin hi`).
- `inertialRD_readsPast` (`InertialRD ρ Δ ⊆ ReadsPast Δ`), `inertialRD_settles`
  (`⊆ SettlesWithin Δ`), **for every `ρ`** (no relation between `ρ` and `Δ` needed).
- `boundedInertial_readsPast`, `boundedInertial_settles` (`[lo, hi]`).
- `rcausal_of_nodeChan`: every node `NodeChan δ D` ⇒ `RCausal δ`.

Soundness in continuous time (same structure as `Ternary`, reusing `Net.cover`,
`resultA_postfix`, `hull_le`, `iterB`).
- `rsound_postfix`: post-fixed point covering the inputs at all times and the
  state at all negative times covers every state, for `RCausal δ`, `δ > 0`
  (induction on `⌈s/δ⌉` via `Archimedean`).
- `rsoundA`, `rnoGlitchA`: algorithm A is sound; a node binary in `resultA` never changes.
- `rsettleB`, `rsettleB_value`: with inputs `= b` from `T0`, every node
  `SettlesWithin D` (`D ≥ 0`), the k-th B-iterate covers every state from
  `T0 + k·D` on.

Corollaries (the requested statements).
- **`ternary_noGlitch_channels`**: every node is a zero-delay gate followed by a
  transport `Chan lo hi` or inertial `BoundedInertial ρ lo hi` channel with
  `lo ≥ δ > 0`; inputs move between `a` and `b` (per input, in any order, even
  back and forth); state `s0` before time 0. A node binary in `resultA` never changes.
- **`ternary_settle_channels`**: add inputs `= b` from `T0` and all `hi ≤ D`. A
  node binary in `resultB` equals that value from `T0 + |ν|·D` on.
- `ternary_noGlitch_channels_pos`: per-node lower bounds `δn i > 0` (no common
  `δ` assumed; finitely many nodes give one, `exists_common_lb`).

Literal `Ternary.Causal` instances (so the original theorems apply verbatim).
- `causal_of_transport`: every node a discrete `TraceDiscrete.Transport lo hi`
  of its excitation with `1 ≤ lo` ⇒ `Causal`.
- `stale_of_transport`: and `hi ≤ D`, `1 ≤ D` ⇒ `Stale D`.
- `causal_of_sample`: grid samples of continuous `Chan` behaviours are `Causal`
  when each excitation is `Discretize.Sep q` and `AtRest` and `1 ≤ L`, `L·q ≤ lo`
  (composition with `Discretize.chan_sample`).

Counterexamples.
- `sample_not_causal`: a buffer, input = runt on `[1/4, 3/4)`, output = input
  delayed by `3/2` (a `Chan 1 2` behaviour). On the grid `q = 1` all input samples
  are `false` and the output sample at 2 is `true`, so the samples are not
  `Causal`, and they violate the conclusion of `noGlitchA` (algorithm A on
  constant `false` inputs gives `0`). Separation (`Sep`) is the missing hypothesis.
- `zero_delay_chan_unsound` (any `hi ≥ 0`), `zero_delay_inertial_unsound` (any
  `ρ`): self-looped buffer, `resultA = 0`, yet a rise at time 1 is a behaviour.

## What it does NOT cover

- A node with lower bound 0 (a zero-delay gate), even in an acyclic part where it
  would be harmless: `RCausal` asks every node for `δ > 0`. Model a zero-delay
  gate followed by a delayed wire as one node (gate + channel), which is what
  `NodeChan` already is.
- Per-pin wire delays inside one node: a node reads all its inputs at one time
  (gate then channel). Separate wire delays are separate buffer nodes (as
  `XSim` does with `Init.delay_buf`); the theorems then apply to that expanded net.
- Involution channels (`Delay/Involution.lean`): not attempted (no
  `InvolutionPair` instance in the build). They are `ReadsPast` only when the
  delay function is bounded below by a positive constant, which is a property
  of the instance.
- Exactness/completeness of ternary simulation: unchanged (Wip/Ternary W1).
- Time `s < 0`: the behaviour is assumed to sit at `s0` there (`h0`).

## Correct wording for the lead (FEASIBILITY §4 and the Ternary.lean header)

Replace the §4 bullet on `Core/Ternary.lean` with:

> - `Core/Ternary.lean` + `Core/TernaryChannels.lean`: Eichelberger ternary
>   simulation is sound for discrete-time causal behaviours (`Causal`, which
>   includes GMW, `gmw_causal`, and discrete transport with lower bound ≥ 1
>   step, `causal_of_transport`), and, in continuous time, for every network
>   whose nodes are zero-delay gates followed by `Core/Delay` transport
>   (`Chan`) or inertial (`InertialRD`/`BoundedInertial`) channels with a
>   positive lower delay bound (`ternary_noGlitch_channels`). Settling
>   (algorithm B) holds within `|ν|·D` for both channel kinds, `D` the largest
>   upper delay bound (`ternary_settle_channels`; for inertial channels via
>   `SettlesWithin`, not `Stale`). A zero lower delay bound makes it unsound
>   (`zero_delay_chan_unsound`, `zero_delay_inertial_unsound`); grid samples
>   of continuous behaviours are `Causal` only under separation
>   (`causal_of_sample`; counterexample `sample_not_causal`). bd_c2's every
>   single-input flip settles with no static hazard. This is a decidable,
>   delay-independent per-cell check.

Ternary.lean header (I did not edit it; for the lead or its owner): the bullet
"This contains the GMW ... and also transport / pure delays ..., inertial
delays, and any mixture" should read "This contains the GMW step relation
(`gmw_causal`) and discrete transport channels with lower bound ≥ 1
(`TernaryChannels.causal_of_transport`). Continuous-time transport and
inertial channels are handled by the real-time analogue `RCausal` in
`TernaryChannels` (positive lower bound needed)." In `notes/A-ternary.md`, W4
("inertial delay → Stale") is closed in the sense that settling for inertial
channels is proved (`ternary_settle_channels`); the `Stale` hypothesis itself
remains false for inertial channels, as the note says.

## The other two audit rows

**pulseWidth (`Delay/Involution.lean:337`, FEASIBILITY §2 "Involution").** The
Lean says: for an `InvolutionPair` with a minimum delay `δmin` (`IsDMin`),
`pulseWidth` is strictly increasing on input widths `> 0`
(`pulseWidth_strictMono`), a pulse of width `Δ > 0` is cancelled
(`pulseWidth Δ ≤ 0`) iff `Δ ≤ δ∞↑ − δmin` (`pulse_cancel_iff`), and for every
`ε > 0` there is `η > 0` with `0 < pulseWidth Δ < ε` for all
`Δ ∈ (δ∞↑ − δmin, δ∞↑ − δmin + η)` (`pulseWidth_small`): the right-hand limit at
the threshold is 0. Continuity at other widths is not stated. Exact wording:

> output pulse width is strictly increasing in the input width; an input pulse
> is cancelled iff its width is ≤ δ∞↑ − δmin (`pulse_cancel_iff`), and just above
> that threshold the output width is positive and tends to 0 as the input width
> decreases to it (`pulseWidth_small`: right-hand limit 0 at the threshold;
> continuity elsewhere is not stated). All under `IsDMin` (existence of δmin is
> a hypothesis).

The current FEASIBILITY text ("tends to 0 as the input width approaches the
threshold (limit at the threshold only; audit wording fix)") is correct except
that "approaches" should be "decreases to" (one-sided, from above) and the
parenthetical can be dropped in favour of the wording above. The Lean docstring
of `pulseWidth_small` ("shrink continuously to zero") overstates in the same
way; suggested docstring: "Output pulses shrink to zero at the cancellation
threshold (right-hand limit): for every `ε > 0`, inputs just above
`δ∞↑ - δmin` give outputs in `(0, ε)`."

**RealComplete (`Trace/Real.lean`, FEASIBILITY §2 table row "ℝ → Bool").** The
hypothesis is discharged: `Trace/Real.lean:516 theorem realComplete :
RealComplete := fun _ hne hbdd => Real.exists_isGLB hne hbdd`, and
`inertial_short'`/`inertial_long'` (:518, :522) are the unconditional versions. The
module header (Real.lean:15 and :352, "taken as the explicit hypothesis
`RealComplete` until ...", "so here it is an explicit hypothesis") is stale as
well. Exact wording:

> B4's "first event" arguments use completeness of ℝ, stated as `RealComplete`
> and proved from Mathlib (`realComplete`, from `Real.exists_isGLB`); the
> inertial B4 results also hold without the hypothesis (`inertial_short'`,
> `inertial_long'`, `Trace/Real.lean:516–524`).

(The current FEASIBILITY line "B4 carries a named hypothesis `RealComplete`,
since discharged from Mathlib (audit: this line was stale)" is acceptable but
self-contradictory in tone: it no longer "carries" a hypothesis.)

## Check result

`formal/check.sh Formal/Core/TernaryChannels.lean` (2026-10-27 ~13:00 UTC):
`[check] textual scan` / `[check] lean …` / `[audit] 833 declarations checked` /
`[check] OK`. Plain `lake env lean` gives no errors and no warnings.
Imports: Ternary, Delay.Pure, Delay.Inertial, Trace.Discrete, Discretize
(the last pulls Net.Prelim and Cells.CElemTiming, only for `causal_of_sample`),
plus `Mathlib.Basic.Real.Basic`, `Mathlib.Algebra.Order.Archimedean.Real.Basic`.

Lead to-do: add `import Formal.Core.TernaryChannels` to `Formal.lean` (no
lakefile change: it is under `Formal/`).
