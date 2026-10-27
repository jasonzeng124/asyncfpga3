# A-discretize: discretisation soundness (continuous ℝ → discrete ℕ time)

Namespace `Formal.Core.Discretize`. This note answers the conjecture W3 of
`A-trace-discrete.md`: when do discrete-time (`ℕ`, 1 step = quantum `q`)
proofs by shards B and C say something about continuous time?

## Files

- `formal/lean/Formal/Core/Discretize.lean`: 735 lines, **proved**. It
  imports `Formal.Core.Trace.Discrete`, `Formal.Core.Delay.Pure`,
  `Formal.Net.Prelim` (shard C) and `Formal.Cells.CElemTiming` (shard B). It
  copies none of their definitions.
- `formal/lean/Wip/Discretize.lean`: 3 open statements, each with `sorry`. It
  elaborates.

Check (from `formal/lean`):

    ../check.sh Formal/Core/Discretize.lean     # [audit] 324 declarations checked, [check] OK
    ../slot.sh lake env lean Wip/Discretize.lean # 3 sorry warnings, no errors

Results:
- No `sorry`, `axiom` or `native_decide`.
- The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.
- The remaining warnings are the Mathlib deprecation notices that every
  ℝ file here gets.
- Checking takes about 10 s.

## Definitions

- `Sep q x`: **H-SEP**, no two transitions within one quantum. For all
  a ≤ b ≤ c with c − a ≤ q, x b = x a or x b = x c.
  - For `Bool` this is equivalent to "no excursion shorter than q"
    (`sep_bool_iff`).
  - For a tuple of nets it means *joint* separation: the tuple changes at
    most once per window.
- `AtRest x`: **H-REST**, x is constant on (−∞, 0]. This matches the discrete
  convention that a signal is constant before step 0.
- `sample q x k = x (k·q)`: sampling at grid points.

## What is proved

**One channel.**
- **`chan_sample`**: assume `DelayPure.Chan lo hi x y`, `Sep q x`,
  `AtRest x`, `L·q ≤ lo` and `hi ≤ H·q`. Then
  `TraceDiscrete.Transport L H (sample q x) (sample q y)`.
  - The tightest choice is **L = ⌊lo/q⌋, H = ⌈hi/q⌉**, which is the bound the
    conjecture expected. Rounding down is necessary:
    `lo_round_down_needed` gives a clean edge, fixed delay 3/2 and q = 1,
    which no discrete channel with L = 2 admits. The mirror case for H is
    Wip W2.
  - **Only the channel input needs H-SEP. The output does not.**
  - Proof idea: for output step k, the read time σ(kq) lies in grid cell m.
    The warp picks m if x(mq) equals x(σ(kq)), and m+1 otherwise. H-SEP makes
    that choice correct and monotone.
  - `Archimedean ℝ` is not built here, so the proof does not use floor.
    The cell is found by least-element search, and the channel bound supplies
    the witness.
- **`sep_out`**: `Sep (q + (hi−lo)) x` implies `Sep q y`. A channel narrows
  pulses by at most hi − lo, so per-net separation propagates if pulse widths
  carry that margin.
- **`chan_sample_hull`**: sound **without** H-SEP. There is a warp f with
  bounds [L, H] such that output sample k equals x at some time in grid cell
  `[f k·q, (f k+1)·q]`. A sample stands for the *set* of values in its cell,
  which is ternary X when the input moves inside the cell. This is the hook
  to a Kleene discrete model (Wip W3).

**Gates and circuits.**
- **`gate_sample` (n-input) and `gate2_sample`**: a zero-delay function g
  followed by a channel. The hypothesis is **joint** separation of the gate's
  input tuple. Equivalently, `sep_map` reduces it to separation of the gate's
  *excitation*.
- **`circuit_sample`**: `CCircuit` is a conjunction of gate relations over a
  net type N. Assume the bundle `Discretizes q C L H v`, which contains:
  - `q > 0`;
  - grid-enclosing bounds;
  - Sep and AtRest of every excitation.

  Then every continuous behaviour, sampled, is a behaviour of the widened
  `DCircuit`.
- **`transfer`**: any property proved for all discrete behaviours holds of
  the samples of every continuous behaviour.
- **`transfer_invariant`**: a state invariant proved at every discrete step
  holds at every grid point k·q.

**Between grid points.**
- **`stable_between` / `stable_interval`**: let z be `Sep q` and equal to v at
  grid points K1..K2. Then z = v on the whole real interval [K1·q, K2·q].
  - So "stable on [a, b]" in real time follows from discrete stability on
    [⌊a/q⌋, ⌈b/q⌉], an interval less than one quantum longer at each end.
  - This needs Sep of *that* net. Sep of the excitation feeding it is not
    enough, because the channel may narrow a pulse; use `sep_out`.
- **`invariant_everywhere`**: let the tuple of nets be JOINTLY `Sep q` and
  AtRest. Then an invariant that holds at all grid points holds at every real
  t.
  - The proof carries the side condition `∃ T, t ≤ T·q`. That is the
    Archimedean property, which is always true but not built in this Mathlib.
  - Wip W1 removes the side condition once
    `Mathlib.Algebra.Order.Archimedean.Real.Basic` is built.

**Counterexamples: separation cannot be dropped** (q = 1).
- Signals: `up` rises at 1/4, `dn` falls at 1/2, and `runt = up ∧ dn` is high
  on [1/4, 1/2).
- **`runt_no_transport`**: `runt` goes through a fixed delay 3/4, which is a
  behaviour of any band containing 3/4.
  - The input samples are all `false`.
  - The output sample at 1 is `true`.
  - **No** discrete `Transport L H` relates them, for any L and H.
- **`tie_counterexample`**: the same situation as an AND gate. Each input is
  a single clean edge (`Sep 1` alone) and the pair is at rest, but the
  sampled circuit is not a discrete behaviour for any bounds.
  - Corollary `tie_not_sep`: the input pair is not jointly separated. Joint
    separation is therefore necessary; per-net H-SEP, as A-trace-discrete.md
    phrased it, is **not sufficient**.
  - **This is exactly the arbiter runt case of `bd_arb.v`.** Take set =
    r1·¬r2 with r1 rising and r2 rising within one quantum.
    - The excitation of `q = C(r1, ¬r2)` has a sub-quantum runt.
    - Sampling makes the runt a "plain tie": set and reset are both 0 in
      every sample, which is `tie_no_glitch` in Discrete.lean.
    - The continuous channel may pass the runt onto a grid point, or partly
      commit the loop.
    - So a discrete proof that "on a tie q holds" does **not** transfer to
      real time for skews below one quantum.
- **`mutex_between`**: ¬(g1 ∧ g2) holds at every sample, while both g1 and g2
  are high at t = 3/8. A grid-point mutual-exclusion theorem (for example
  grant exclusion) says nothing between grid points unless the grants are
  *jointly* separated.

**Bridges to the other shards.**
- **`transport_boundedDelay`**: the FIFO warp channel refines shard C's
  `Formal.Net.BoundedDelay` (both cause and settle).
- **`chan_sample_bd`**: from the continuous channel directly to
  `BoundedDelay`.
- **`chan_sample_win`**: from the continuous channel to shard B's
  `CElemTiming.WinDelay`. It needs no AtRest.
- **`loop_of_continuous`**: assume a continuous feedback-LUT behaviour (the
  LUT excitation through [dlo, dhi], the feedback wire through [wlo, whi]),
  with the excitation and O each `Sep q`. Then its samples form a
  `CElemTiming.Loop` with widened bounds. Consequently `c2_follow_hold`,
  `c2_reset` and `c2_four_phase` hold at every grid point of every such
  continuous behaviour, and with `stable_interval` they hold on real
  intervals.

## Not done (Wip/Discretize.lean)

- **W1**: `invariant_everywhere` without the Archimedean side condition.
  Blocked on the Mathlib module only. About 5 minutes once it is built.
- **W2**: H must be rounded up (the counterexample is stated; the concrete
  witness is in a comment). About 20 minutes.
- **W3**: `chan_hull_out`, the output-hull form of `chan_sample_hull`, then a
  Kleene discrete circuit whose channels carry cell hulls (X if the net
  moves inside a cell). This is the discretisation that stays sound
  *without* H-SEP, and it would let shard B's `ArbKleene` cover the
  sub-quantum runt.
  - The one-channel statement is about 1 h.
  - Defining the Kleene circuit and transferring it is about 0.5 to 1 day.

## Verdict

**Works.** Discretisation soundness is proved, in a form that is sharper
than the conjecture in three ways:
1. The bounds are exactly [⌊lo/q⌋, ⌈hi/q⌉], with no extra quantum.
2. H-SEP is needed only on channel inputs, that is, on gate *excitations*.
3. Separation must be *joint* over each gate's fan-in, not per net. The
   counterexample proves that this is necessary.

About 2.5 h. Effort to finish:
- W1 + W2: under 1 h.
- W3: about 1 day.

**What it buys:**
- Every discrete-time theorem of shards B and C now transfers to real time,
  at grid points, for every continuous FIFO-transport behaviour that
  satisfies H-SEP. Shard B's C-element loop is already bridged
  (`loop_of_continuous`).
- The transfer to whole real intervals costs one quantum per end.
- The discrete representation (Lean core, `omega`) can stay the working one,
  and real time costs one named hypothesis.
- It also shows precisely where that hypothesis fails: arbiter ties within q.
  There the Boolean discrete proofs say nothing, and the hull/Kleene
  discretisation (W3) is the sound replacement.

## Fidelity notes

- **Continuous model.**
  - `DelayPure.Chan` is FIFO transport with a zero-delay Boolean function in
    front. It is the lumped-gate model, not the LUT mux-tree.
  - The mux-tree and Kleene refinements are separate tracks.
  - The soundness theorem relates the two *models*. It says nothing new
    about silicon.
- **H-SEP is a hypothesis about the Boolean model, not the silicon.** Real
  edges have slews of tens of ps, so at q = 1 ps "two transitions of one
  gate's fan-in within 1 ps" is a physically meaningful event: it is an
  input skew below 1 ps.
  - For data paths under the bundling constraint it is generically false
    only on a measure-zero set of skews. It is not *provably* excluded,
    though, and independent inputs (arbiter requests, any asynchronous
    environment) violate it with positive probability per event, of order
    q / (window).
  - Proofs that rely on H-SEP must therefore either be about circuits
    without uncontrolled ties, or use W3 (hull/Kleene).
- **How to test H-SEP.**
  - Board-fidelity GLS (claude/research): log every event on every net and
    report the minimum, over each LUT, of the time between successive
    events across its input pins. Any value below q flags a gate where the
    discretised proof does not apply.
  - Board: not observable below about 10 ps. The arbiter MTBF measurement
    (`cells/verify/MTBF.md`) is the relevant experiment for the sub-quantum
    regime.
- **H-REST** (all excitations constant before 0) is the power-up
  convention. It is satisfiable by holding reset through configuration.
  `chan_sample_win` and the shard-B bridge do not need it.
- **Quantum.** q = 1 ps widens each arc by less than 1 ps at each end, which
  is negligible against the hundreds of ps of routing scatter. A coarse q
  widens every arc by up to q and makes H-SEP more often false.
