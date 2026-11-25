# A-trace-discrete: trace benchmark in discrete time (`ℕ → Bool`)

Track 2, representation (c). Namespace `Formal.Core.TraceDiscrete`.

## Files

- `formal/lean/Formal/Core/Trace/Discrete.lean` (505 lines): B0 through B5 and
  four `decide` checks. **Lean core only, no Mathlib import.** It checks clean:
  no sorry, axiom or native_decide. `formal/check.sh Formal/Core/Trace/Discrete.lean`
  gives `[audit] 59 declarations checked`, `[check] OK`. The axioms used are
  `propext`, `Quot.sound` and in places `Classical.choice`. The `decide`
  theorems use only `propext`, or no axioms at all.
- `formal/lean/Wip/TraceDiscrete.lean` (70 lines, NOT proved): W1, the event
  form of the channel and its equivalence to the warp form; W2, a greedy
  decision procedure for the channel relation on a finite prefix, with its
  soundness and completeness statement; W3, discretisation soundness, as
  prose only. It checks, with 2 `sorry` warnings, once the module's olean
  exists, which `check.sh FILE` builds.

Check commands (from `formal/lean`, with `~/.elan/bin` on PATH):

    ../slot.sh lake env lean Formal/Core/Trace/Discrete.lean   # ~12 s total
    ../check.sh Formal/Core/Trace/Discrete.lean                # + axiom audit, ~23 s

About 10 s of the check time is the 256-input bounded model check
(`bmc_inertial_min_width`). Without it the file checks in about 3 s.

## Representation

- `Sig := Nat → Bool`. One step is one quantum q, for example 1 ps.
- **Before time 0 every signal is constant at its value at step 0.** Truncated
  subtraction gives this for free: `s (t - d)` reads `s 0` when `t < d`.
- A transition at `t+1` means `s (t+1) ≠ s t`.
- **B0 has no well-formedness condition.** Finite variability is automatic
  (`trCount_le`: at most n transitions in n steps). The initial value is `s 0`.
  The minimum pulse width is one quantum, by construction.
- **Bounded transport channel = monotone time warp.**
  `Transport lo hi i o := ∃ f, Warp lo hi f ∧ ∀ t, o t = i (f t)`, where
  `Warp` is: f is monotone, `f t ≤ t - lo` and `t - hi ≤ f t`. Each output
  step shows the input as it was between lo and hi steps earlier, and the
  sampling point never moves backwards.
- **Order-crossing: transitions never cross. They can collide and
  annihilate.** Because o = i ∘ f with f monotone, a pulse can come out
  narrower, wider or not at all, but never split or inverted
  (`pulse_convex`). Two input transitions whose delays bring them onto the
  same step cancel each other, and that is how a pulse is lost (`pulse_lost`).
  The same channel also admits passing the short pulse unchanged
  (`pulse_may_pass`), so the channel is nondeterministic about short pulses.
  The event form (each transition gets a delay in [lo,hi], arrivals
  non-decreasing, two arrivals on one step cancel) is stated in Wip W1. W1 is
  not proved. The proof sketch: pick f t between the last arrived input
  transition and the next one, and every inequality needed is one-line
  arithmetic.

## Benchmark results

| item | theorems (all proved) | lines | wall time | pain |
|---|---|---|---|---|
| B0 | `trCount_le`; helpers `exists_tr` (discrete IVT), `exists_least` | 50 | 10 min | core has no `Nat.find` (Mathlib's `Data.Nat.Find` is not built), so I proved `exists_least` myself (10 lines) |
| B1 | `delay_delay`, `delay_zero` | 14 | 2 min | none: `funext; omega` |
| B2 | `transport_comp`, `transport_mono`, `delay_transport`, `transport_exact` (lo=hi gives exactly B1), `transport_cause` (every output transition has an input cause with delay in [lo,hi]), `transport_isolated` (an input transition isolated by hi−lo on each side gives exactly one output transition, old→new, with delay in [lo,hi]) | 119 | 35 min | comp and mono are 5 lines each. `transport_isolated` took two attempts. The trick is to rewrite the output in the window as `if u < f t then !a else a`, after which everything is `omega` |
| B3 | `pulse_convex`, `pulse_outer` (output pulse ⊆ [p+lo, p+w+hi)), `pulse_inner` (⊇ [p+hi, p+w+lo)), `pulse_interval` (the output pulse is one interval [s,e)), `pulse_width` (e−s ≤ w+hi−lo; and if w > hi−lo, the pulse is present and e−s ≥ w−(hi−lo)), `pulse_lost` (w ≤ hi−lo: the constant output is admitted), `pulse_may_pass` | 104 | 25 min | truncated subtraction near t=0 forced side conditions `1 ≤ p` (the pulse starts after time 0) and `lo ≤ hi`. The lost-pulse witness is an explicit 4-branch warp. Monotonicity is `repeat' split; omega` |
| B4 | `inertial` is a recursive *function* (output takes the input value once the input has been stable on [t−δ, t]). `inertial_filters` (w ≤ δ: output constant), `inertial_passes` (w > δ: output is exactly the pulse shifted by δ, width unchanged), `inertial_change`, `inertial_min_width` (every output pulse is ≥ δ+1 wide) | 119 | 30 min | case analysis on regions of t (`repeat' split at hk` plus `cases a <;> simp_all`) is brute force and slow to write, but it works. Induction on time is plain `Nat` induction, which is easier than the ℝ probe, where B4 needs GLB / Archimedean modules |
| B5 | `AndGate lo hi a b o := Transport lo hi (a && b) o`. `and_follows` (b held at 1 ⇒ o is an [lo,hi] channel of a), `and_chain` (a circuit = conjunction of two AND relations ⇒ [lo1+lo2, hi1+hi2] channel), `and_follows_from` (b = 1 only from step T: from T+hi, o shows a value a had lo..hi steps earlier) | 34 | 10 min | none |
| BMC | `bmc_inertial_min_width` (all 256 inputs of 8 steps, horizon 10, by `decide`), `bmc_inertial_pulse`, `tie_no_glitch`, `skew_glitch` | 40 | 15 min | needs `maxRecDepth`. Cost grows linearly with inputs × horizon² (see below) |

Total: about 2 h, 505 lines, of which about 40% are statements and docstrings.

## Can `decide` do bounded model checks?

Yes, for **closed, finite statements about functions**: deterministic
semantics such as `inertial`, `delay` and gate functions, over enumerated
input patterns (`bits n`), with kernel evaluation and no native_decide.
Measured on this machine (profiler):

| check | inputs × horizon | kernel time |
|---|---|---|
| `inertial 2`, min width | 256 × 10 | ~10 s |
| `inertial 3`, min width | 2048 × 14 | ~110 s (needs `maxHeartbeats 0`) |

Cost is roughly linear in the number of inputs, so exponential in input
length. 2^16 inputs would take hours. The general theorem
(`inertial_min_width`) took about 20 lines and covers all inputs, all horizons
and all δ.

`decide` does **not** handle the relational models directly: `Transport`
quantifies over an unbounded warp `f : ℕ → ℕ`. For bounded checks against the
relation you need a decidable characterisation. Wip W2 gives a greedy one
(take the least feasible `f t ≥ f (t-1)`; least-so-far is optimal). `#eval`
confirms it on examples:
- `delay 2` is in [1,3]: true.
- `delay 5` is in [1,3]: false.
- A lost pulse of width 2 in [0,2]: true.
- The same lost pulse in [0,1]: false.

Its soundness and completeness proof (`admits_iff`) is not done; I estimate
2 to 4 h. Even with it, enumerating behaviours at a 1-ps quantum over
realistic horizons (hundreds to thousands of steps per gate) is far beyond
kernel `decide`. Use an external SAT/SMT/UPPAAL (track 12) for real bounded
model checks, and keep `decide` for unit-level sanity checks at a coarse
quantum.

## What discreteness costs in fidelity

1. **Quantisation of delay bounds.** prjxray SDF arcs are given to 1 ps, and
   `timing.py`'s RC wire model produces fractional ps. With q = 1 ps, rounding
   outward (lo down, hi up) adds at most 1 ps of nondeterminism per arc. That
   is negligible next to this part's routing scatter of hundreds of ps
   (CLAUDE.md) and the 434–945 ps per hop in LIBRARY.md. A coarser quantum,
   for example 10 ps to make `decide` usable, costs up to q per arc, so a
   20-arc path is widened by 200 ps. That is comparable to the guardbands the
   project argues about (200 ps guard, 213 ps margin): **too coarse.** Stay at
   1 ps for proofs.

2. **Gate-by-gate discretisation is not automatically sound.** A real-time
   [lo,hi] channel sampled at the grid gives a discrete [⌊lo/q⌋, ⌈hi/q⌉]
   channel only if the channel's input changes on grid points. Intermediate
   nets in a real circuit do not. The soundness claim per gate, conjectured
   and not proved (Wip W3, prose only, since it needs the ℝ probe's
   definitions):

   > Widen each gate's interval by one quantum, and assume (H-sep) that no
   > net makes two transitions within one quantum. Then the sampled real
   > behaviour satisfies the conjunction of the discrete gate relations.

   H-sep is physically plausible at 1 ps, because edges have slews of tens
   of ps. However, the Boolean model ignores slew, so H-sep is a hypothesis
   about the model, not the silicon. It would have to be a named hypothesis
   in any theorem that transfers results to real time. It is not testable on
   the board below about 10 ps resolution. In GLS it can be tested by
   checking that no net in the board-fidelity GLS (claude/research) has two
   events closer than q. Runt pulses narrower than q are where it fails, and
   those are exactly the arbiter's runts.

3. **Ties.** Discrete time represents simultaneous arrival exactly and makes
   it an ordinary event, not a measure-zero one. `tie_no_glitch`: a rises and
   b falls on the same step, and AND(a,b) has no glitch. `skew_glitch`: one
   step of skew gives a one-step glitch, which a [lo,hi] channel with hi > lo
   may pass or drop (`pulse_may_pass`, `pulse_lost`). This suits the bd_arb
   header's case split:
   - The "plain tie" (both requests rise on the same step: set and reset
     both false, q holds) is expressible directly.
   - The "runt" (r1 and r2 moving in opposite senses within one loop delay)
     is expressible whenever the loop delay is ≥ 2 quanta. It is about 100
     quanta at 1 ps.

   The caution: a discrete tie means "within one quantum". The physical
   sub-quantum skews (where metastability lives) are rounded to tie or to a
   one-quantum runt. Provided the channels around the arbiter have hi > lo
   (plus the one-quantum widening of item 2), the relation admits both
   roundings, so a proof over all behaviours still covers both. What the
   Boolean discrete model cannot represent is the intermediate voltage
   itself. That belongs to track 3 (Kleene X) and track 4 (ODE), not to the
   trace representation.

4. **Primitive fidelity in this file.** Only abstract channels and an
   idealised Boolean AND with lumped delay (`AndGate`) are modelled. That is
   not the LUT mux-tree model the program requires; the LUT model belongs to
   track 4. Transport and inertial delay are the standard abstractions:
   - Transport is sound but loose. It admits pulse loss and stretching within
     ±(hi−lo).
   - Inertial delay with a fixed δ is not a physical 7-series primitive. The
     involution channel is the faithful candidate (sibling probe).

## Verdict

**Works.** All of B0 to B5 are proved in about 2 h, about 500 lines, with
Lean core only and no Mathlib (fast checking, and immune to the partial
Mathlib build). It was the cheapest of the representations for:
- B0, which needs no well-formedness condition;
- B4, which uses ordinary `Nat` recursion and induction rather than
  infima/GLB;
- everything else, because `omega` closes all the arithmetic.

`decide` gives free unit-level bounded checks.

Costs:
- truncated-subtraction edge cases near t = 0 (extra `1 ≤ p` and `lo ≤ hi`
  hypotheses);
- brute-force `repeat' split; omega` proofs;
- the fidelity argument for discretisation (item 2) is an extra hypothesis
  (H-sep plus one quantum of widening per gate), and its transfer proof to
  real time is open.

**Recommendation:** use discrete time (q = 1 ps) as the working
representation for gate-level proofs and for the verified timing checker
(track 10: integer ps delays, `omega`, and computable checkers). State H-sep
explicitly. If track 2 needs real-time results, prove W3 once against the ℝ
probe's definitions rather than redoing every lemma over ℝ.

Effort to finish the open items:
- W1 (event form ⇔ warp): 3 to 5 h.
- W2 (greedy checker sound and complete): 2 to 4 h.
- W3 (discretisation soundness, needs the ℝ probe): 1 to 2 days.

What it buys: a Mathlib-free core that every other shard can import cheaply.
Gate relations become plain `Prop`s over `Nat` that `omega` handles, and
deterministic sub-models can be sanity-checked by `decide`.

## Comparison-ready table

| item | proved? | Lean lines | wall time | main pain |
|---|---|---|---|---|
| B0 signal type, non-Zeno | yes (`trCount_le`) | 50 (incl. IVT, least-element helpers) | 10 min | no `Nat.find` in core |
| B1 fixed delay, composition | yes (`delay_delay`) | 14 | 2 min | none |
| B2 bounded transport: comp, mono, no-spurious, isolated propagation | yes (`transport_comp`, `transport_mono`, `transport_cause`, `transport_isolated`) | 119 | 35 min | the isolated-transition step argument |
| B3 pulse width, loss, no inversion | yes (`pulse_width`, `pulse_interval`, `pulse_convex`, `pulse_lost`, `pulse_may_pass`) | 104 | 25 min | t=0 edge cases (`1 ≤ p`, `lo ≤ hi`) |
| B4 inertial filter / pass | yes (`inertial_filters`, `inertial_passes`, `inertial_min_width`) | 119 | 30 min | brute-force region case splits |
| B5 AND gate relation, circuit, b=1 property | yes (`and_follows`, `and_chain`, `and_follows_from`) | 34 | 10 min | none |
| BMC by `decide` | yes, 4 closed checks | 40 | 15 min | exponential; 2048×14 ≈ 110 s |
| event form ⇔ warp (W1) | no (Wip, sorry) | 15 | - | not attempted |
| relation decision procedure (W2) | no (Wip, sorry; `#eval` works) | 20 | - | proof not attempted |
| discretisation soundness (W3) | no (prose) | - | - | needs ℝ probe and H-sep |
| Mathlib needed | none | | | |
| check time | ~3 s (+10 s for the 256-input BMC) | | | |
