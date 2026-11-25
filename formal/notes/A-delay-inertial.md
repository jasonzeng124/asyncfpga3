# A-delay-inertial: track 3, delay channel (b), inertial delay

Probe of the inertial delay channel in continuous time. Namespace
`Formal.Core.DelayInertial`. The probe is self-contained: a signal is `ℝ → Bool`.
The representation probe picks the final signal type. Nothing here needs finite
variability, because each theorem is about the signals it names.

## What checks

`formal/lean/Formal/Core/Delay/Inertial.lean` checks with no errors and no
`sorry`/`admit`/`axiom`/`native_decide`/`bv_decide`. `#print axioms` on the main
theorems (run on a scratch copy) gives only `propext, Classical.choice, Quot.sound`.

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    ../slot.sh lake env lean Formal/Core/Delay/Inertial.lean

The output has only deprecation warnings: the `Mathlib.Data.Real.Basic` import, and
`if_pos`/`if_neg`.

### Definitions

- `Stable x τ ρ` means x is constant on [τ, τ+ρ).
- `FiltAt ρ x b u` and `Filt ρ x z` define the zero-delay rejection filter. The output
  at u is `x τ` for the latest τ ≤ u with `Stable x τ ρ`. The definition is a
  relation; the "latest" condition is stated as "every later stable τ' ≤ u has the
  same value".
- `InertialRD ρ Δ x y := Filt ρ x (fun u => y (u+Δ))` is an inertial channel with
  rejection window ρ and delay Δ. In Verilog terms this is a path delay Δ with a
  PATHPULSE reject limit ρ.
- `Inertial δ := InertialRD δ δ` is the classic Verilog/iverilog default.
- `BoundedInertial ρ lo hi x y := ∃ Δ ∈ [lo,hi], InertialRD ρ Δ x y` has a rejection
  window plus one delay per instance that is fixed but unknown.
- `NoShort ρ x` says that every constant run of x starts with at least ρ of
  stability, i.e. x has no pulse shorter than ρ.
- `shift Δ` is a pure transport delay.
- `pulse b a w` is b everywhere except ¬b on [a, a+w).

Why this matches the event-queue rule: an input change at t schedules its value at
t+δ, and a later change before t+δ cancels it. So the changes that survive are
exactly those followed by at least δ of stability. The latest surviving change is
the latest stable window start. On ties, a change at exactly t+δ does not cancel.
The full equivalence with an event-list algorithm is stated in Wip (item 1); it is
not proved.

### Theorems (all in `Formal.Core.DelayInertial`)

| theorem | content |
|---|---|
| `filtAt_unique`, `filt_unique`, `inertialRD_unique` | the channel relations are functional |
| `inertialRD_pulse_short` (+`_exists`), `inertial_pulse_short` | a pulse with w < ρ is removed and the output is constant |
| `inertialRD_pulse_long` (+`_exists`), `inertial_pulse_long` | a pulse with w ≥ ρ passes as `pulse b (a+Δ) w`: same width, delayed by Δ |
| `inertialRD_const` | constant input gives the same constant output |
| `inertial_width_discontinuous` | for every ε there are input widths w₁ < w₂ = δ less than ε apart: w₁ gives no output, w₂ gives an output pulse of width δ. The width map jumps 0 → δ |
| `noShort_of_inertialRD` | for **every** input, the output has no pulse shorter than ρ |
| `inertialRD_output_pulse_width_ge` | if the output is a single pulse of width w > 0, then w ≥ ρ ("no runts") |
| `inertialRD_solves_boundedSPF` | one inertial channel meets the single-pulse bounded-SPF conditions (see below) |
| `inertialRD_of_noShort` | **on inputs with no pulse shorter than ρ, an inertial channel is a pure transport delay** |
| `boundedInertial_pulse_short`, `_long`, `_long_exists`, `boundedInertial_no_runt` | the same results for the bounded-delay variant; every Δ ∈ [lo,hi] is realised |
| `inertialRD_comp`, `inertialRD_comp_iff` | if ρ₂ ≤ ρ₁, then `InertialRD ρ₁ Δ₁ ; InertialRD ρ₂ Δ₂ = InertialRD ρ₁ (Δ₁+Δ₂)` |
| `inertial_comp_self` | `Inertial δ ; Inertial δ = InertialRD δ (2δ)` (the filter is idempotent) |
| `inertial_comp_ne_sum` | for all δ₁, δ₂ > 0, `Inertial δ₁ ; Inertial δ₂ ≠ Inertial (δ₁+δ₂)`. A pulse of width max(δ₁,δ₂) passes the cascade, but the summed channel removes it |
| `inertial_order_matters` | `Inertial 1 ; Inertial 2` and `Inertial 2 ; Inertial 1` give different outputs on `twoPulse` |
| `inertial_comp_1_2_not_inertialRD` | `Inertial 1 ; Inertial 2` is not `InertialRD ρ Δ` for **any** ρ, Δ |

### The true composition relation

The cascade puts the larger rejection window first:

    InertialRD ρ₁ Δ₁ ; InertialRD ρ₂ Δ₂ = InertialRD ρ₁ (Δ₁+Δ₂)   when ρ₂ ≤ ρ₁.

The proof uses two facts. The first filter's output has no pulse shorter than ρ₁.
On such signals the second filter is the identity.

When ρ₂ > ρ₁, the cascade is not any inertial channel. Take the input `twoPulse`:
high on [0, 3/2) and on [2, 7/2), so two 3/2 pulses with a 1/2 gap. The width-1
filter fills the gap and produces one 7/2 pulse, which the width-2 filter then
passes. A filter with window wider than 3/2 removes both pulses. A filter with
window at most 3/2 passes a lone 3/2 pulse that the cascade removes. So inertial
channels are not closed under composition, and the pulse-shaping behaviour of a
chain of inertial LUTs depends on the order of their delays. The sum never works:
a pulse of width max(δ₁,δ₂) separates the cascade from `Inertial (δ₁+δ₂)`.

## The unfaithfulness result (stated, not proved)

The citations are from memory. Check the exact hypotheses against the papers
before quoting them in FEASIBILITY.md.

- M. Függer, T. Nowak, U. Schmid, "Unfaithful glitch propagation in existing binary
  circuit models", ASYNC 2013; journal version IEEE Trans. Computers 65(3):812–825,
  2016.
- M. Függer, R. Najvirt, T. Nowak, U. Schmid, "Towards binary circuit models that
  faithfully capture physical solvability", DATE 2015.
- M. Függer, R. Najvirt, T. Nowak, U. Schmid, "A faithful binary circuit model",
  IEEE TCAD 39(10), 2020. This is the involution channel.

**Short-Pulse Filtration (SPF).** The circuit has one input and one output, and the
input is either constantly 0 or a single pulse. A solution must satisfy four
conditions:

- (no generation) with no input pulse, there is no output transition;
- (non-triviality) some input pulse produces an output transition;
- (no short pulses) there is ε > 0 such that the output never contains a pulse shorter than ε;
- (bounded SPF only) the output stabilises within a bounded time after the input does.

**Theorem (FNS 2016, informal).** Physically, using continuous-valued circuits,
bounded SPF cannot be solved. This is a continuity argument: the output must
depend continuously on the input pulse width. Every binary model whose channels are
bounded single-history channels can solve bounded SPF. In those channels, an output
transition's delay depends only on the time since the previous output transition,
and it is bounded. Pure delay, inertial delay and (as I recall) the DDM all fall in
this class. So none of these models is faithful. Involution channels (FNNS 2020)
make bounded SPF unsolvable and unbounded SPF solvable, as physics does.

**What is proved here.** `inertialRD_solves_boundedSPF` shows that one inertial
channel alone satisfies all four conditions for single-pulse inputs, with ε = ρ and
settling time Δ after the input settles. This is the witness half of the
unfaithfulness result for this channel. `inertial_width_discontinuous` exhibits the
discontinuity that makes it possible. The physical half (no continuous circuit
solves bounded SPF) is not formalised. It needs an analog model and is outside this
track.

## Fidelity: what this means for iverilog GLS and for C-element/latch proofs

`cells/gls/prims.v` makes wires transport delays (`-DGLS_TRANSPORT_IC`). LUT, MUXF7/8,
carry and FF paths use specify-block module-path delays, which iverilog treats as
inertial with reject limit = delay. A LUT has one path per input pin
(`(A1 => O6) = TA1O6`, …), so its δ depends on which pin changed, and a rise and a
fall may differ. `Inertial δ` is the single-δ idealisation of that. The
per-pin/per-edge case is in Wip items 2 and 3, and is not proved.

Consequences:

1. **A GLS pass is not evidence of runt-freedom at a LUT output.**
   `noShort_of_inertialRD` proves that an inertial LUT can never emit a pulse
   shorter than its path delay. A glitch narrower than the path delay vanishes in
   simulation, whatever its source: input skew through different-delay paths, or a
   hazard. The LUT is a zero-time mux tree in the sim, so internal hazards are not
   modelled at all. On silicon such a glitch may come out as a runt, a full pulse,
   or nothing, and it can be fed back. bd_ce's C-element is a LUT6 whose own O
   drives I2, and bd_latch's storage loop is Q = EN ? D : Q. A runt on that
   feedback can flip or metastabilise the stored state, and the sim cannot show it.

2. **Inertial is not a conservative abstraction in either direction.** It drops
   behaviour silicon has: a short pulse that physically propagates or degrades into
   a runt. It also adds behaviour silicon lacks: a pulse of width exactly δ passes at
   full width δ, where physics attenuates it continuously (FNS). So a proof of a
   C-element or latch that relies on inertial filtering transfers neither to silicon
   nor from GLS. **C-element/latch proofs must never use the filtering property as a
   hypothesis.**

3. **The bridge that is sound: `inertialRD_of_noShort`.** If the input to a LUT's
   output channel has no pulse shorter than ρ, the inertial channel is exactly a pure
   delay. Here the input is the zero-time LUT function of its pin signals, after
   pin delays. Then the GLS behaviour and the transport-delay model agree. They
   should also agree with an involution channel, which is the identity on long
   pulses up to delay (to be proved in the involution probe). The recommended proof
   shape for each storage cell is therefore:
   - (a) prove that under the bundled-data environment assumptions, the LUT
     function's value never has a pulse shorter than ρ. This is hazard-freedom
     under bounded skew, and it needs the LUT Kleene/hazard hypothesis from the
     lut-tree probe: no output glitch when all selected cofactors agree, e.g. the
     latch's EN falling while D = Q.
   - (b) conclude that the delay-channel choice is irrelevant for that cell.
   Wherever (a) fails, the cell's correctness depends on unmodelled glitch
   behaviour, and both the proof and the GLS are void there.

4. **Tests of the hypotheses.**
   - (i) GLS: rebuild with LUT specify paths replaced by transport assignments (as
     already done for wires) and with `+pulse_r/0 +pulse_e/0`, or with
     `PATHPULSE$` set to 0, so short pulses pass. Then diff the waveforms of every
     C-element and latch input against the inertial run. Any difference marks a cell
     that relies on filtering.
   - (ii) Board: drive a LUT input with a controlled-width pulse made by a
     two-path skew; sweep the width through the LUT delay and capture the output
     with a toggle counter. The prediction to test is whether the output pulse-count
     curve is a step at δ (the inertial claim, refuted if it is not) or a smooth
     ramp (involution).

## What does not check, and why

The open items are in `formal/lean/Wip/DelayInertial.lean`, as statements with
`sorry`. That file imports the Formal module and is not built.

1. Equivalence of the semantic `Filt` with an explicit event-list (toggle-time)
   algorithm, which is what Verilog does (`inertial_eq_queue`). It also gives
   existence of outputs for finitely-variable inputs (`filt_exists`). This is
   ordinary list induction over ℝ and has no obstacle.
2. A per-transition nondeterministic bounded inertial channel, where each
   surviving change has its own delay in [lo,hi]. The expected width bound is
   w ± (hi − lo).
3. Asymmetric rise/fall delays. iverilog's exact cancellation rule there is
   unverified: check IEEE 1364-2005 §14.6 and a two-LUT probe first.
4. The physical (analog) half of the FNS impossibility.

## Verdict

**Works.** The single-δ and (ρ, Δ) inertial channels, the bounded variant, pulse
filtering and passing, the discontinuity, the no-runt property, and the exact
composition law with its counterexamples are all proved in about 600 lines. Each
file check takes about 15 s. The relational-with-uniqueness style worked well: every
"output equals …" theorem is a witness plus `inertialRD_unique`. Linarith did the
real arithmetic; nothing else beyond the three permitted Mathlib modules was needed.

**Effort to finish.**
- Wip item 1 (event-list equivalence and existence): about 1–2 days.
- Per-transition bounded variant: about 1 day.
- Asymmetric rise/fall: about 1 day once the iverilog rule is pinned down by experiment.

**What it buys the project.**
- It turns "iverilog's inertial LUT delays swallow narrow pulses" into theorems:
  `noShort_of_inertialRD` (GLS can never show a LUT runt) and
  `inertialRD_output_pulse_width_ge`.
- It gives the one sound bridge between GLS and the proof model,
  `inertialRD_of_noShort`, so cell proofs know exactly what side condition
  (no LUT-function pulse shorter than the path delay) makes the delay-channel choice
  irrelevant.
- It formally documents why inertial is not a faithful channel: the SPF witness and
  the discontinuity, and the fact that inertial channels are not closed under
  composition.

For the core model: use inertial only to describe what the GLS does, never as the
channel that silicon proofs rely on. The faithful channel for proofs is the
involution channel (other probe) or a nondeterministic over-approximation.
