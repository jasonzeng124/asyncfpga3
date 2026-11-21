# B probe 5d: the `bd_c2` loop on shard A's continuous-time channels

File: `formal/lean/Formal/Cells/CElemCore.lean` (about 916 lines; imports
`Formal.Cells.Prelim`, `Formal.Cells.CElemTiming`, shard A's
`Formal.Core.Delay.Pure` and `Formal.Core.Delay.Inertial`, plus Mathlib
`Algebra.Order.Archimedean.Real.Basic`, `Topology.Order.IntermediateValue`,
`Topology.MetricSpace.Pseudo.Lemmas`, `Topology.Algebra.Ring.Real`).

Check command (once lake has built `Formal.Core.Delay.*`):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH ../slot.sh lake env lean Formal/Cells/CElemCore.lean

Status: checks clean, 0 errors, 0 warnings, in about 12 s. Shard A's
`Pure.lean`/`Inertial.lean` had no oleans yet, so I compiled them from their
unchanged sources into my scratchpad (`lean -o`, through `slot.sh`; this was
not a `lake build`) and checked against those together with the Mathlib
oleans that already existed. No `sorry`/`admit`/`axiom`/`native_decide`.
`#print axioms` on all 12 main theorems shows only `propext`,
`Classical.choice` and `Quot.sound`.

## 1. 5b restated on A's channels (`Chan`: FIFO bounded pure delay, ℝ time)

`LoopR init a b rst O qp dlmin dlmax dwmin dwmax`:
* `H_LUT : Chan dlmin dlmax (excR …) O`. The excitation is `CElemTiming.exc`,
  which is `lutB` on the REAL INIT `0x00E8…`.
* `H_FB : Chan dwmin dwmax O qp`.
* `H_LOOP_POS : 0 < dlmin + dwmin`.
* `H_CAUSAL : 0 ≤ dlmin ∧ 0 ≤ dwmin`. This is new: in ℕ it held
  automatically. It is needed in the four-phase proof.

Theorems (windows are now half-open, which reads more cleanly than 5b's `t+1 ≤ …`):
* `exc_held`, `O_held`, `qp_held` (any INIT): forced for `Dmax`, then a fixed
  point up to `t2`, gives excitation `= v` on `[t0,t2)`, `O = v` on
  `[t0+dlmax, t2+dlmin)` and `qp = v` on `[t0+Dmax, t2+Dmin)`.
* (a) `c2_follow_hold`, `c2_reset`: the same statements as in 5b.
* (b) `runt_loopR` + `runt_oscillatesR`: for any `dl, dw ≥ 0` with `D > 0` and
  `0 < w < D`, the closed-form traces satisfy every gate relation (with
  `dlmin=dlmax=dl`, `dwmin=dwmax=dw`). After `t0+w` the inputs are constant
  (`a=1,b=0,rst=0`), yet `qp(t0+(n+1)D) = 1` and `qp(t0+(n+1)D+w) = 0`
  for every `n`, and the same holds for `O`. So the `Dmax` pulse-width bound
  is still tight.
* (c) `c2_four_phase`: the same hypotheses as in 5b (`H_ALT`, `H_ORDER`,
  `H_BOTH`, `H_NEXT`, `H_NORST`, `H_ACK`, `H_ENV_LATENCY : Dmax ≤ dlmin + E`,
  `H_RESET_DONE`). Conclusion: `O = V k` on `[c k + dlmax, c(k+1) + dlmin)`
  and `qp = V k` on `[c k + Dmax, c(k+1) + Dmin)`.

What changed between ℕ and ℝ:
* The settle-and-hold proof can no longer use strong induction on time. It
  becomes induction on `n` over the windows `[t0, t0 + Dmax + n·Dmin)`, plus
  the Archimedean property (`exists_mul_gt`). That is about 10 extra lines,
  and the argument is otherwise the same.
* A's channel is a monotone read-time map `σ`, not 5b's per-tick window. The
  proofs only use `s - hi ≤ σ s ≤ s - lo`, so nothing else changed. FIFO
  is not needed for the positive results.
* Negative delay bounds must be excluded explicitly (`H_CAUSAL`).
* The runt counter-trace became EASIER. `train` is defined as
  `∃ n, t0+nD ≤ t < t0+nD+w` instead of with `mod`, so the loop equation is
  a one-line recursion (`train_rec`: split on `n = 0` or `n = m+1`). The only
  real work is a cast argument (`train_period`: if `t` lies in period `n`,
  the witness is `n`).
* `linarith` handles all the interval arithmetic, including terms like
  `(n+1)·D`. In ℕ, `omega` did that job, but `Nat.mod` needed manual rewrites.
* Overall, ℝ costs about 20% more proof text for (a) and (c) and less for (b).

## 2. Inertial LUT in the loop

Model (`InLoop`): `H_LUT_INERTIAL : InertialRD ρ dl (excR …) O` (A's
rejection filter with window `ρ`, then a shift by `dl`); `H_FB : qp t = O(t-dw)`
(fixed wire, A's `Chan dw dw` by `chan_fixed_iff`); `H_INIT : qp = 0` before
the runt. Inputs: `a = 1`, `rst = 0`, `b = pulse false t0 w` (A's `pulse`).
The loop delay is `D = dl + dw`.

* `filtAt_congr`: A's filter is local. Its value at `u` depends only on the
  input before `u + ρ`.
* `inLoop_unique` (any INIT, any inputs): the inertial loop is DETERMINISTIC.
  Two solutions whose `qp` agree before `t0` agree everywhere. Hypothesis
  `H_CAUSAL_LOOP : ρ < dl + dw`: the filter looks `ρ` ahead, so the loop must
  not see its own future. The proof is induction on windows of length
  `D - ρ`, then Archimedes. With uniqueness, each regime below reduces to
  checking one explicit solution.
* (i) `inertial_lost`: if `w < ρ` (and `ρ < D`), then `O ≡ 0` and `qp ≡ 0`.
  The event is LOST. This is 5b's ℕ result, now proved for every solution.
* (ii) `inertial_circulates`: if `ρ ≤ w` and `ρ ≤ D - w`, every solution is
  the train. `qp = 1` at `t0+(n+1)D` and `qp = 0` at `t0+(n+1)D+w` for all
  `n`: it oscillates forever. The key lemma is `train_noShort`: a train
  whose pulses and gaps are all `≥ ρ` passes the filter unchanged.
* (iii) `inertial_latches`: if `ρ ≤ w` and `D - w < ρ` (the gap is shorter
  than the window), every solution is the step: `O = 1` from `t0 + dl` on,
  forever. `filt_latch` proves directly that the filter fills the gap. This
  also covers `w ≥ D`, where there is no gap at all.
* `runt_below_D_can_latch` REFUTES the informal 5b claim that
  "`ρ ≤ w < D` circulates". With `ρ=1`, `dl=dw=1`, `w=3/2`, the loop latches.
  The claim is false on all of `(D-ρ, D)`.

The exact picture for the inertial loop (with `ρ < D`):
`w < ρ` is lost, `ρ ≤ w ≤ D-ρ` oscillates forever, and `w > max(ρ, D-ρ)`
latches. Tie convention: a gap of exactly `ρ` passes (A's `Stable` is
`[τ, τ+ρ)`).
* If `2ρ > D`, the oscillation band is EMPTY. For the classic inertial delay
  (`ρ = dl`) that means `dw < dl`: when the feedback wire is faster than the
  LUT, the model never oscillates. Every runt is then decided (lost or
  latched) by `t0 + dl`, a bounded time independent of `w`. This is the
  bounded short-pulse filtration (SPF) that real circuits cannot do, the same
  unfaithfulness A proved for the bare channel (`inertialRD_solves_boundedSPF`).
* If `2ρ ≤ D`, the bad regime is a whole interval of widths, not a single
  point. That is also unphysical: real loops oscillate only at isolated
  critical widths (see 3).
* From the C-element's point of view, latching (iii) is the CORRECT outcome
  (`a = b = 1` did happen, and `a=1,b=0` means hold). Lost (i) is a missed
  event, which deadlocks the handshake. Oscillation (ii) is the worst case.

## 3. Involution channel

Shard A had no involution channel (`git log -- formal/lean/Formal/Core`:
only Pure and Inertial). I could not fetch the paper: arxiv.org and hal
are unreachable from this container (DNS fails, proxy returns 403). I took
the definition from memory and the search-result abstracts (TCAD 2020,
doi 10.1109/tcad.2019.2937748; arXiv 1406.2544). Those abstracts confirm:
bounded SPF is unsolvable with involution channels, and unbounded SPF is
solvable.

Minimal definition (`InvCh`, all fields are named hypotheses):
* delay functions `dU`, `dD : ℝ → ℝ`;
* `dUinf = δ↑(∞)`;
* `H_CONT`: `dU`, `dD` are continuous;
* `H_MONO`: `dU`, `dD` are monotone;
* `H_INV`: `-dU(-dD T) = T` and `-dD(-dU T) = T`;
* `H_POS`: `dU 0 > 0` and `dD 0 > 0`;
* `H_INF`: `dU 0 < dUinf`.

The channel rule: an input transition at `t`, with the previous output
transition at `o`, produces an output transition at `t + δ(t - o)`. Out-of-order
output transitions cancel each other.

The loop (`a=1`, `rst=0`) is the OR storage loop `x = b ∨ qp`: a zero-time
LUT function followed by ONE involution channel (LUT and wire lumped). The
runt is `b = [0, Δ0)`, `0 < Δ0 < dUinf`. Output transition times:
* `o 0 = dUinf` (rise);
* `o 1 = Δ0 + dD(Δ0 - dUinf)` (fall);
* after that `x = qp`, so `o(n+2) = o n + δ_n(o n - o(n+1))`, with `δ_n = dU`
  for even `n` (`InvCh.orb`).

The first `n` with `o(n+1) ≤ o n` is a cancellation: an even `n` means LOST
(the output stays 0), an odd `n` means LATCHED (it stays 1). `Osc Δ0` means
no cancellation ever happens.

Theorems:
* `inv_eternal`: for EVERY involution channel there is a runt width
  `Δ0 ∈ (dUinf - dU 0, dUinf)` for which the C-element loop oscillates
  forever (never resolves). Proof:
  * the lost set `Lset` and the latched set `Hset` are open, since the
    `o n` depend continuously on `Δ0`;
  * a tie `o(n+1) = o n` is resolved two steps later by the involution law
    at `T = 0` (`cover`); this is what makes the two sets open and covering;
  * the two sets are disjoint (the first cancellation index is unique);
  * the left endpoint is lost: `o 1 = dUinf - dU 0 < o 0`;
  * the right endpoint is latched: `o 2 = o 0 < o 1`;
  * `[dUinf - dU 0, dUinf]` is connected, so some width in it is neither
    lost nor latched.

  The proof needs no fixed point, no IVT on an explicit map, and no
  concavity.
* `osc_unbounded`: on an oscillating orbit the output transitions go to
  infinity. There is no Zeno behaviour: `o(n+2) ≥ o n + p` with `p > 0`,
  taken from continuity at 0 together with the involution law. So the output
  keeps switching after every time bound.

Answer to the probe's question: under the involution model the C-element
loop does NOT resolve a runt in bounded time. There is a critical width that
never resolves, which is the binary-model analogue of metastability. By
continuity, nearby widths resolve only after arbitrarily long times; this
last step follows from openness of `Lset`/`Hset` but is NOT stated as a
separate theorem. This contrasts with the inertial model, which decides
every runt by `t0 + dl` or oscillates on a whole interval of widths.

Not proved / gaps:
* The recurrence `orb` is derived from the channel rule in the docstring.
  It is NOT derived from a signal-level involution channel relation on
  `ℝ → Bool`, because no such relation exists in Core yet. A Core channel
  (transition sequences, cancellation) plus a lemma that the OR loop's
  sequence is `orb` would close this; estimate half a day.
* "Resolution time unbounded near the critical width" is not stated as a
  theorem: for each `N`, some width completes `≥ N` periods and then
  resolves. It follows from `inv_eternal` plus continuity of the `o n`;
  estimate one to two hours.
* Uniqueness of the critical width and instability of the periodic orbit:
  these need concavity of `δ` (the paper assumes it); not attempted.
* No noise or adversarial variation (`η`-involution, DATE 2018).

## Verdict

**Works.** Everything planned is proved in about 1.5 h. Finishing the
involution part (a Core involution channel relation and the "≥ N periods
then resolves" corollary) would take about 1 day.

What it buys the project:
* The 5b timing results now hold on shard A's real-time channels.
* The inertial picture is corrected: the circulation band is
  `[ρ, D-ρ]`, not `[ρ, D)`, and it is empty when `2ρ > D`.
* There is a formal argument that the inertial model is unfaithful for this
  loop: it gives bounded resolution, or an interval of eternal oscillation.
* A positive, gate-level metastability result for the feedback-LUT
  C-element under the involution model: an unresolvable runt width always
  exists, whatever the delay functions. For the GLS this means that runts
  near the critical width must be expected to circulate for a long time. A
  timing checker must therefore ENFORCE the `Dmax` minimum pulse width
  (5b/5d (a), (c)), because it cannot rely on runts dying out.

## Fidelity per primitive

* LUT: the binary Boolean function from the REAL INIT through `lutB`
  (`exc`, `c2_eq`). No mux-tree, X or runt-shaping behaviour inside the
  LUT. In (1) its delay is a FIFO band; in (2) it is A's inertial filter
  (a modelling alternative, unfaithful as shown); in (3) the LUT and the
  wire are lumped into one involution channel behind a zero-time Boolean
  function (the paper's gate model; this lumping is not proved equivalent
  to two channels in series).
* Feedback wire: in (1) a FIFO band `[dwmin, dwmax]` (prjxray min/max of the
  routed net); in (2) a fixed delay; in (3) part of the lumped channel.
* All three channel models are single-delay abstractions of the R/C-shaped,
  slew-dependent real behaviour. Involution channels are the only one of
  the three that the paper proves faithful for SPF. Its delay functions
  would be fitted from SPICE or GLS pulse-shrink measurements (test: the
  output pulse width vs input pulse width curve of one LUT plus route at the
  slow and fast corners).
