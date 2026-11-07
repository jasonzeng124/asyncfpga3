# A-trace-real: trace benchmark in continuous time (`ℝ → Bool`)

Track 2, representation (a). Namespace `Formal.Core.TraceReal`.

Files:
- `formal/lean/Formal/Core/Trace/Real.lean` (511 lines): B0-B5, all proved. It
  checks clean, with no sorry, axiom or native_decide. `#print axioms` on the
  main theorems (including `inertial_long`) shows only
  `propext, Classical.choice, Quot.sound`. The B4 theorems take the completeness
  of ℝ as an explicit hypothesis `RealComplete` (GLB property), because the
  Mathlib module that proves it has not been built yet (see "B4 status").
- `formal/lean/Wip/TraceReal.lean`: discharges `RealComplete` with
  `Real.exists_isGLB` (3 short theorems). **Not checked yet**: it needs
  `Mathlib.Algebra.Order.Archimedean.Real.Basic`, which is requested in
  `Wip/REQUESTS.txt`.

Check command (from `formal/lean`, PATH includes `~/.elan/bin`):

    ../slot.sh lake env lean Formal/Core/Trace/Real.lean

Imports: `Mathlib.Basic.Real.Basic` (the new name of the deprecated
`Mathlib.Data.Real.Basic`) and `Mathlib.Tactic.Linarith`. `ring` is not
available, so equalities are proved with `linarith`. Checking takes about 5 s
once the imports are built.

## Representation

- `Val := Bool`, `Sig := ℝ → Val`.
- `WF s`: at every `t` there is an `ε > 0` such that `s` is constant on `[t, t+ε)`
  (right-continuity) and constant on `(t-ε, t)` (a left limit exists). This is
  the *local* form of non-Zeno behaviour. By compactness it is equivalent to
  "finitely many transitions in every bounded window", but that equivalence is
  not proved, because it would need compactness of `Icc`.
- `ConstBefore T s`: the initial value. It is kept separate from `WF` because
  channels shift the "initial" time.
- `Trans s t`: on some `(t-ε, t)` the value differs from `s t`. This is a
  transition at `t`.

## Results per item

| item | statement | Lean name(s) | status |
|---|---|---|---|
| B0 | signals, WF, transitions; constants and pulses are WF | `WF`, `Trans`, `ConstBefore`, `wf_const`, `pulse_wf` | proved |
| B1 | `delay d₂ ∘ delay d₁ = delay (d₁+d₂)`; WF preserved; transitions shift exactly | `delay_delay`, `delay_zero`, `delay_wf`, `delay_trans_iff` | proved |
| B2 | transport channel `TChan lo hi`: composition, monotonicity, fixed delay is an instance, transitions map one to one with delay in [lo,hi], order preserved, no extra output transitions, output WF | `Warp.comp`, `tchan_comp`, `tchan_mono`, `delay_tchan`, `tchan_trans_iff`, `tchan_trans_in`, `tchan_trans_out`, `tchan_wf` | proved |
| B2' | sampling-window channel `Window lo hi` (sound over-approximation): TChan ⊆ Window, composition, monotonicity, stable-input lemma | `tchan_window`, `window_comp`, `window_mono`, `window_stable` | proved |
| B3 | pulse width `w` through TChan comes out as one pulse of width in `[w-(hi-lo), w+(hi-lo)]`, always `> 0`; through Window it is lost when `w ≤ hi-lo` and kept when `w > hi-lo` | `tchan_pulse`, `tchan_pulse_width_pos`, `tchan_pulse_not_lost`, `window_pulse_lost`, `window_pulse_kept` | proved |
| B4 | inertial `δ`: a pulse with `w ≤ δ` gives no output at all; a pulse with `w > δ` comes out as `pulse (a+δ) w` | `RealComplete`, `Inertial`, `first_change`, `inertial_short`, `inertial_long` | proved, with `RealComplete` as a hypothesis (a Mathlib theorem whose module is not built yet; discharge in Wip) |
| B5 | `Gate2 ch f a b y`; with `b ≡ 1`, AND follows `a` (TChan and Window versions); local window version; a circuit of two chained ANDs, defined as the conjunction of gate relations, follows `a` within `[lo₁+lo₂, hi₁+hi₂]` | `Gate2`, `and_follows`, `and_follows_window`, `and_window_local`, `AndChain`, `andChain_follows` | proved |

### Key design decision (B2): the channel as a time warp

`TChan lo hi x y := ∃ θ, Warp lo hi θ ∧ ∀ t, y (θ t) = x t`, where `θ` is a
strictly increasing surjection `ℝ → ℝ` with `θ t - t ∈ [lo, hi]`. The
event-level reading in the benchmark is *derived*, not assumed:
- every input transition `t` gives an output transition at `θ t`
  (`tchan_trans_iff`);
- order is preserved (`StrictMono`);
- every output transition comes from an input transition, with a delay in
  `[lo, hi]` (`tchan_trans_out`, which uses surjectivity).

For WF signals, the converse also holds informally: any order-preserving
choice of per-transition delays in `[lo,hi]` extends to a warp by piecewise
linear interpolation. So `TChan` is exactly "order-preserving bounded
transport". With this definition, composition and monotonicity are about
10 lines each, because warps compose by function composition. This is the
strongest point of the ℝ representation.

### Order crossing (B3): how it is handled

- In `TChan`, order crossing **cannot be expressed**. A pulse of any width
  `w > 0` survives with width `> 0` (`tchan_pulse_width_pos`,
  `tchan_pulse_not_lost`). In a function `ℝ → Bool`, an "inverted" pulse
  (falling edge before rising edge) has no meaning: the output can only show
  the pulse, nothing, or a glitch. So `TChan` is **unsound for the silicon**
  for pulses shorter than about `hi - lo`, because real paths can swallow runts.
  Use it only together with a hypothesis that pulses are wider than `hi - lo`.
- `Window lo hi` (the output at `t` equals the input at *some* instant in
  `[t-hi, t-lo]`) is the sound, conservative channel. For `w ≤ hi-lo` it
  admits losing the pulse (`window_pulse_lost`); for `w > hi-lo` the pulse must
  appear (`window_pulse_kept`). The price is that it also admits glitches
  (several output transitions for one input transition, inside the window). So
  hazard-freedom proofs cannot use it; they need TChan, inertial or involution.

### B4 status

`first_change` is the "induction over time" principle for continuous traces.
It says: if `y v₀ = b` and `y t ≠ b`, then there is a transition `s ∈ (v₀, t]`
with `y s ≠ b`. Its proof takes the GLB of `{u ∈ [v₀,t] | y u ≠ b}` and uses
right-continuity. It needs only right-continuity, not the left-limit half of
WF. Both B4 theorems then follow by a four-region case split. ℝ's completeness
(`Real.exists_isGLB`) lives in `Mathlib.Algebra.Order.Archimedean.Real.Basic`,
which has not been built yet. It is therefore the named hypothesis
`RealComplete : ∀ S : Set ℝ, S.Nonempty → BddBelow S → ∃ g, IsGLB S g`.
This is a mathematical fact, not a modelling assumption. Once the module
exists, the lead (or a follow-up) should move the three lines in
`Wip/TraceReal.lean` into `Real.lean`, which removes the hypothesis. The
inertial relation is:

    Inertial δ x y :=
      (∀ t, x constant on [t-δ, t] → y t = x t) ∧
      (∀ t, Trans y t → x constant on [t-δ, t])

It is deterministic for WF outputs, but the existence of an output for every
WF input is not proved.

## What was painful

- **Induction over time needs completeness.** Any argument of the form "the
  first time the output does X" (B4, and any safety proof about feedback
  circuits) needs a GLB argument, as in `first_change`. Once proved it can be
  reused, but every such proof needs the WF signal hypotheses and a case split
  over time regions with `linarith`.
- **Region proofs.** `pulse_wf` alone is 35 lines of choosing ε per region.
  Every concrete waveform costs that much, so in practice explicit waveforms
  should be built from helpers (`pulse_in`/`pulse_out`/`pulse_const_*`).
- **Decidable trouble.** `pulse` must be `noncomputable` (ℝ comparisons). `rw`
  under `decide` fails on motive typing; `simp only` works.
- **Mathlib drift.** The import has to be `Mathlib.Basic.Real.Basic`, `push_neg`
  is deprecated (use `push Not`), and `ring` is not built.
- **Pleasant.** Pure delay and warp composition are near-trivial (funext plus
  `linarith`). Window channels compose in 5 lines. `linarith` closes almost
  every arithmetic side goal.

## Fidelity (gate-fidelity rule)

- **Binary values.** This hypothesis is implicit in `Val = Bool`. Runt and
  metastable intermediate voltages are not representable. Kleene or analog
  tracks must cover them.
- **`TChan` (order-preserving transport).** It is faithful only for pulses
  wider than `hi - lo` along the path. It is unsound for shorter pulses, which
  silicon may swallow or shrink. To test: a GLS or board pulse-width sweep
  through a LUT/route chain (a pulse-shrinking ring), measuring the output
  width against the input width.
- **`Window` (sampling).** It is sound for any binary-valued element whose
  output at `t` was the input's value at some instant within its delay
  window. That is the weakest assumption, and the recommended default for
  safety proofs. Testable as: no output value at `t` is unseen on the input
  in `[t-hi, t-lo]`, using prjxray fast/slow min/max for lo/hi.
- **`Inertial δ`.** It is an idealisation with a sharp rejection threshold.
  Real LUTs and pips have a soft threshold: pulses near `δ` come out
  shortened (this is the involution channel's behaviour). Treat `Inertial` as a
  hypothesis to be validated, not as a fact about the fabric. To test: the same
  pulse-width sweep, which locates the cut-off and the width-transfer curve.
- **Gates (`Gate2`).** A Boolean function in front of a channel. This is the
  LUT-as-Boolean-function abstraction, so it is not the pass-transistor mux
  model the program asks for. Glitches due to internal mux structure are
  covered only through `Window`'s nondeterminism.

## Verdict

**It works.** B0–B5 are all proved in 511 lines. B4 is modulo `RealComplete`,
a Mathlib theorem whose module has not been built yet. Expected effort to
finish: about 5 minutes once the module exists (check the Wip file, then move
it in). Wall time: about 1.5 h, including about 30 min waiting for the Mathlib
build.

What it buys the project:
- the most natural statement of delay-channel semantics, with trivial
  composition through warps;
- real arithmetic, for free, for the timing checker (track 10) and the analog
  ODE track (same `ℝ`);
- a sound `Window` channel.

What it costs:
- every causal or first-event argument goes through completeness (one generic
  `first_change` lemma helps);
- concrete waveforms are verbose;
- nothing is computable or decidable, so there is no `decide`-style
  automation and no executable simulation.

## Comparison table

| item | proved? | Lean lines | wall time | pain points |
|---|---|---|---|---|
| B0 defs/WF | yes | ~25 (+70 pulse helpers and `pulse_wf`) | 10 min | ε choices per region for concrete waveforms |
| B1 pure delay | yes | ~36 | 5 min | none (`ring` missing → `linarith`) |
| B2 bounded transport | yes | ~123 (composition and monotonicity ~25; event-level lemmas the rest) | 20 min | none for composition; the transition correspondence needs surjectivity arguments |
| B2' window channel | yes | ~36 | 5 min | none |
| B3 pulses | yes | ~40 (+ helpers above) | 15 min | `decide` and rewriting; crossing is impossible in TChan, so Window is needed for loss |
| B4 inertial | yes (with `RealComplete` as a hypothesis) | ~130 (`first_change` 40, the two theorems 90) | 30 min | needs completeness of ℝ (missing module, so it is a hypothesis); four-region case split; `simp` on `decide` failed, so helpers are needed |
| B5 AND gate, circuit | yes | ~36 | 5 min | none |
