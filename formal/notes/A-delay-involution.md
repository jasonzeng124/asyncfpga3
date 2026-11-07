# A / track 3c: involution delay channels

Probe: formalize the involution channels of Függer, Najvirt, Nowak and Schmid
("Towards binary circuit models that faithfully capture physical solvability",
DATE 2015; "A faithful binary circuit model", IEEE TCAD 2020; the earlier
arXiv 1406.2544, "Faithful glitch propagation in binary circuit models"), prove
the basic lemmas, and judge whether shard B's C-element and arbiter proofs should
use them.

**Verdict: works.** The core theory checks in 535 lines using only
`Mathlib.Basic.Real.Basic` plus linarith, ring and norm_num. One shortcut: the
exp-channel uses `exp` and `log` as abstract functions with named hypotheses (see
the exp-channel section below). The real instance is drafted in Wip and waits for
the Log module. Using involution channels in cell proofs works with effort; see
the assessment section.

Source caveat: WebFetch and curl could not reach arxiv, HAL or TU Wien from this
sandbox (DNS or proxy refusal). Web-search snippets confirmed the following:
- the involution property;
- that `−δ` mirrored about `T = −δ(T)` is an involution;
- that the delay functions are strictly increasing and concave;
- that bounded SPF is unsolvable and unbounded SPF is solvable with involution
  channels;
- that the model has been validated against SPICE and measurements.

The definitions below come from memory of the papers and were checked for
internal consistency. I derived the exp-channel formula myself from the RC
trajectory and proved it is an involution. Its symbols may differ from the
paper's, but the function should be the same.

## What checks

Command (from `formal/lean`):

    ../slot.sh lake env lean Formal/Core/Delay/Involution.lean

The file is clean: no errors, no warnings, and no `sorry`, `axiom` or `native_decide`.
`#print axioms` on `pulseWidth_small`, `cancel_iff` and `exp_pulse_cancel_iff`
reports only `propext`, `Classical.choice` and `Quot.sound`.

Everything is in namespace `Formal.Core.DelayInvolution`.

**Model.** `InvolutionPair` holds the following fields, each a named hypothesis:
- `up` and `down`, with limits `infUp = δ∞↑` and `infDown = δ∞↓`, both positive;
- domains and ranges `up : (−δ∞↓,∞) → (−∞,δ∞↑)` and `down : (−δ∞↑,∞) → (−∞,δ∞↓)`;
- strict monotonicity;
- the involutions `−δ↑(−δ↓T) = T` and `−δ↓(−δ↑T) = T`;
- strict causality `δ(0) > 0`.

Concavity, continuity and the limit at ∞ are **not** used by any theorem here.
δmin is the hypothesis `IsDMin d`, meaning `δ↓(−d) = d`. In the paper its
existence comes from the intermediate value theorem.

| theorem (in `InvolutionPair`) | content |
|---|---|
| `up_neg_down`, `down_neg_up`, `neg_down_mem`, `neg_up_mem` | consequences of the involution property |
| `down_surj`, `up_surj` | δ↓ attains every value below δ∞↓, at the explicit point `−δ↑(−v)` (no IVT needed) |
| `down_lt_iff`, `up_lt_iff`, `neg_down_strictAnti` | order reflection; `−δ↓` is strictly decreasing |
| `IsDMin.up_fix` | δ↑(−δmin) = δmin: **both directions share δmin** |
| `IsDMin.unique`, `IsDMin.pos`, `IsDMin.lt_infUp`, `IsDMin.lt_infDown`, `IsDMin.lt_up_zero`, `IsDMin.lt_down_zero` | 0 < δmin < δ(0) < δ∞, and δmin is unique |
| `gapUp_strictMono`, `gapDown_strictMono`, `gapUp_nonpos_iff`, `gapDown_nonpos_iff` | `T + δ(T)` is strictly increasing and ≤ 0 exactly when T ≤ −δmin |
| `tent`, `tent_le`, `dom_ok` | channel semantics on a strictly increasing sequence of alternating input transitions. The first transition gets δ∞, and each later one gets `t + δ(t − o_prev)`. Every argument is proved to lie in its delay function's domain |
| `cancel_iff` | output `n+1` is not after output `n` (so the pair annihilates) **iff** `t(n+1) − o(n) ≤ −δmin`, in both directions |
| `pulseWidth_eq`, `pulse_cancel_iff` | an isolated input pulse of width Δ is cancelled iff Δ ≤ δ∞↑ − δmin |
| `pulseWidth_strictMono` | the output width is strictly increasing in Δ |
| `pulseWidth_small` | for every ε > 0 there is η > 0 such that each Δ in (δ∞↑−δmin, δ∞↑−δmin+η) gives an output width in (0, ε). Output pulses shrink continuously to 0, the property that makes the model faithful to SPF. The proof is an ε–η argument from the explicit surjectivity, with no topology library |
| `pulseWidth_lt` | output width < Δ + (δ∞↓ − δ∞↑), the per-stage stretch of a long pulse |
| `up_bounds`, `down_bounds` | if T ≥ T0, then δ(T) ∈ [δ(T0), δ∞): **under an input-separation hypothesis an involution channel is a bounded pure delay** |
| `inertialWidth`, `inertial_gap` | contrast: an inertial channel never emits a pulse of width in (0, D) |

**Exp-channel** (namespace `ExpLog`). Its physical setup: a pure delay `T_p`,
then a first-order RC stage that switches at threshold 1/2 and starts from the
voltage the previous opposite transition left behind. This gives

    δ(T) = T_p + τ·ln(2 − e^{−(T+T_p)/τ}),   δ∞ = T_p + τ ln 2.

`exp` and `log` are an abstract `ExpLog` structure whose fields are named
hypotheses: E > 0, E strictly increasing, E 0 = 1, L∘E = id, and E∘L = id on
positive numbers. The intended model is `E x = e^{x/τ}`, `L y = τ ln y`.

Proved:
- `exp_inv`: the involution property, by exact algebra;
- `exp_dom`, `exp_lt`, `exp_strictMono`, `exp_causal`: domain, range, strict
  monotonicity and causality, assuming T_p > 0;
- `expPair`: the channel as an `InvolutionPair`;
- `exp_dmin`: **δmin = T_p**;
- `exp_pulse_cancel_iff`: a pulse is cancelled **iff Δ ≤ τ ln 2**.

## What does not check (Wip/DelayInvolution.lean, not built)

- `realExpLog` and `real_exp_pulse_cancel_iff`: the real instance, with
  `E = exp(·/τ)` and `L = τ·log`. These are drafted against Mathlib names but not
  checked, because they need `Mathlib.Analysis.SpecialFunctions.Log.Basic`. I
  appended that module to `Wip/REQUESTS.txt`. The Wip file also imports the
  `Formal.Core.Delay.Involution` module, so it needs that module's olean as well.
- `exists_dmin` (sorry): existence of δmin from continuity. It needs an
  IVT module from `Mathlib.Topology.Order`. Until then, `IsDMin` is a hypothesis.
- `filtered_output_trace` (sorry, placeholder statement): the full output trace
  with chained cancellations, i.e. the paper's algorithm as a function from input
  traces to output traces, and its agreement with `tent`/`cancel_iff`. I only did
  the local rule and isolated pulses. Writing the full trace semantics is roughly
  1–2 days. The effort is mainly in choosing the representation and connecting it
  to the shared trace type from track 2, which was not yet in Core when I wrote
  this.
- **Not done:** the paper's actual SPF impossibility theorem (no circuit solves
  bounded SPF). That proof is a continuity argument over whole circuits: output
  traces depend continuously on input traces. It needs the full trace semantics
  plus topology. I estimate 1–3 weeks, and it is research-level formalization.

## Assessment: should the C-element and arbiter proofs (shard B) use involution channels?

**Cost compared with bounded pure delay.**
- An involution channel is deterministic and has one history variable, the time of
  the previous output. In a circuit the gate becomes "zero-time Boolean (or
  Kleene) function + channel". Each proof then carries one extra real per channel
  and the cancellation case split.
- To cover PVT and routing variation it must be quantified (`∀ P : InvolutionPair`
  with δ∞ and δmin in given intervals), or replaced by η-involution channels
  (Függer, Maier, Najvirt, Nowak, Schmid, DATE 2018, adversarial noise η). In
  Lean, quantifying over `P` turns the deterministic channel into the relation
  that PROGRAM.md asks for, so it fits the "gates are relations" layering.
- For **protocol proofs** of the C-element, latch and link under a well-behaved
  environment, `up_bounds` and `down_bounds` give a clean reduction. Assume a
  separation hypothesis: every input transition comes at least T0 after the
  channel's previous output. The channel then behaves exactly like a bounded pure
  delay in [δ(T0), δ∞), with no cancellations, because T0 > −δmin gives positive
  gaps by `cancel_iff`. **Recommendation:** shard B proves the cells against
  bounded pure delay and states the separation hypothesis. The result then
  transfers to involution channels by `up_bounds`, `down_bounds` and `cancel_iff`,
  at an extra cost of about one lemma per cell.
- Involution channels are needed only where pulses are short or glitchy: runts,
  hazards, and the arbiter's set/reset runt. There, bounded pure delay is
  **unsound**: it never shortens or cancels pulses, so it treats every runt as a
  full pulse. Inertial delay is **unfaithful**, because `inertial_gap` makes
  bounded SPF solvable, and that is physically impossible.

**What the faithful-model SPF result says about `bd_arb`.**
- The papers' result: in the involution model, bounded-time SPF is unsolvable and
  unbounded SPF is solvable, which matches physics. The arbiter's storage loop
  `q = C(r1, ~r2)` is the same structure as the paper's SPF circuit, an OR or
  C-element with feedback through a channel.
- A runt on set/reset (r1 and r2 moving in opposite senses within one loop delay)
  enters the loop as a short pulse. `pulseWidth_small` shows the model has
  arbitrarily short pulses near the cancellation threshold, so the loop can
  produce a pulse train whose resolution time is not bounded.
- The binary model therefore **reproduces the qualitative fact**: no bounded-time
  guarantee that q settles, hence no unconditional handover exclusion bound for
  bd_arb. It shows this without postulating metastability.
- It **cannot** give a probability or an MTBF, because the binary model has no
  measure on input timings. The e^{−t/τ} law and its rate still need the analog
  layer (track 4) plus a timing distribution. This is consistent with PROGRAM.md's
  expected result: only a probabilistic bound holds.
- It also rules out a class of fixes. The project's overlap filter
  (`raw & delay(raw)`, ARBITER.md) is a bounded SPF attempt. By the
  faithful-model theorem, no binary circuit makes that filter exact. The measured
  passband (≤ 80 ps blocked, ≥ 160 ps passed at W = 1) must contain a continuum
  of attenuated pulses between the two. That is consistent with
  `pulseWidth_small`, and it is why a W-link filter can only measure "ambiguity
  outliving ~W·delay", as ARBITER.md already says.
- The "+68 ps stretch each O6 LUT adds to a positive pulse" in ARBITER.md is, in
  this model, δ∞↓ − δ∞↑ ≈ 68 ps for that arc (`pulseWidth_lt`, as a bound).
- The unexplained 8% of grant overlaps falls below what the flow's timing model
  can express. A pulse-shrinking channel like this one is a candidate mechanism
  that a pure-delay model cannot represent, but I have not checked that.

## Fidelity to 7-series silicon

- **What the model assumes.** A single-input, single-output channel whose output
  depends only on the time since its last output, with a 1/2 threshold
  (first-order RC). The papers validate it against SPICE and measurements for
  CMOS inverter chains, with known inaccuracies for multi-input gates (MIS
  effects, which Ferdowsi et al. treat with hybrid models).
- **Where a LUT differs.** A LUT is a pass-transistor mux tree behind input
  buffers and an output buffer. Its select-to-output path is several RC stages,
  and different pins have different arcs. The involution channel is at best a
  per-pin, per-edge fit, so δ↑ and δ↓ must be **per (pin, edge)**.
- **Assumptions to test:** (H1) the involution property holds for a LUT arc;
  (H2) δmin and δ∞ are stable per routed arc; (H3) an exp-channel fits within
  tolerance ε.
- **How to test them.** GLS cannot test any of these, because it is purely
  digital and SDF delays are pure or inertial. A board experiment can:
  - Inject pulses of controlled width Δ, from a carry-chain or IDELAY vernier,
    through a chain of N identical LUT stages.
  - Measure the surviving width with a TDC, and fit the per-stage map
    Δ ↦ Δ'.
  - The model predicts a strictly increasing map with a cancellation threshold
    δ∞↑ − δmin, outputs continuous down to 0, and long-pulse offset
    δ∞↓ − δ∞↑.
  - The involution itself is checked with pairs of transitions:
    δ↓(T) followed by δ↑(−δ↓(T)) should return −T.
  - ARBITER.md's passband table and the +68 ps O6 stretch are coarse existing
    data points.
- **Routing:** buffered pips are plausibly involution-like. Pass-transistor pips
  are RC; a first-order RC is exactly the exp-channel's derivation, but chained
  RC is not first-order.

## Effort and value

- **Done:** core theory, lemmas, and the exp-channel modulo `exp` and `log`,
  about 2.5 hours.
- **To finish:**
  - the real `exp`/`log` instance: 1 hour after the module builds;
  - δmin existence: half a day after an IVT module builds;
  - the full trace semantics: 1–2 days;
  - the circuit-level bounded-SPF impossibility theorem: 1–3 weeks.
- **What it buys the project:**
  - a faithful channel for exactly the cases bounded pure delay gets wrong (runts
    and the arbiter loop);
  - a proved reduction to bounded delay for the well-separated protocol case, so
    shard B can keep the simpler model;
  - a formal reason, short of analog modelling, why bd_arb's exclusion cannot be
    an unconditional theorem and why the overlap filter can only be
    threshold-relative.
