# B probe 7f: soundness of two-phase ternary simulation (H_TERNARY_SIM)

File: `formal/lean/Formal/Cells/TernarySound.lean` (core Lean, imports
`Formal.Cells.Prelim` and `Formal.Cells.ArbKleene`; no Mathlib; ~900 lines).
New local definitions (all in this file, nothing added to Prelim): the
information order `le`, a pointwise list relation `Pw` (core Lean has no
`List.Forall2`), a general LUT network `Circ` (`Src`, `Node`), the ternary
Jacobi step `stepK` / `iter`, the binary trace model `Run` / `Bounded`, and
the arbiter instance `arbNet` with the encoding `enc` of 7b's state.

Check (clean, no output, ~2 s):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/TernarySound.lean

`#print axioms` on all main theorems: `[propext, Quot.sound]`, plus
`Classical.choice` for `algA_terminates`/`algA` (a proof by contradiction).
No sorry / admit / axiom / native_decide; `scan.py` passes.

## The delay model (stated precisely)

Discrete time ℕ. A binary trace is `v : ℕ → ℕ → Bool` (step, node). A network
`Circ` has nodes that are `input`s or `gate init pins` (a LUT: its real INIT,
pins = node indices or tied constants). A `Run` is a trace plus read times
`rd k j p` with

* **H_WIRE_CAUSAL** `rd k j p ≤ k`: pin `p` of gate `j` at step `k` sees its
  source's value at some earlier (or the same) step. One read time PER PIN,
  unbounded, varying, not necessarily FIFO: strictly weaker than pure,
  inertial or bounded wire delay, so it covers all of them.
* **H_GMW_GATE**: `v (k+1) j = v k j ∨ v (k+1) j = lutB init (pins as read)`.
  Each gate independently holds or takes its current LUT value: Brzozowski
  and Seger's GMW (general multiple-winner) model, unbounded gate delay, and
  (via per-pin reads) unbounded wire delay.

Inputs are unconstrained except by the ternary input vector (`admits`), so
an input "changing" during phase A may do anything (runts, glitches, several
toggles), not just one clean edge.

For convergence (Algorithm B, bounded form) additionally `Bounded R D W`:
* **H_WIRE_BOUND** `k ≤ rd k j p + W`.
* **H_GATE_BOUND**: if a gate's LUT value is `b` at every step of
  `[k, k+D]`, its output is `b` at some step of `[k, k+D+1]`.

Non-vacuity: `unitDelay_run` proves the synchronous unit-delay binary
simulation `simB` (any input trace, any initial state) is a `Run` with
`Bounded … 0 0`. (An earlier draft of H_GATE_BOUND, "a gate is unequal to
its excitation for at most D steps", was rejected because a unit-delay ring
oscillator violates it, which would have made oscillating networks vacuous.)

## Theorems (namespace `Formal.Cells.TernarySound`)

**(1) LUT facts.**
* `lutK_mono`: `Pw le zs zs' → le (lutK init zs) (lutK init zs')`
  (monotonicity in the information order, `x` on top). Via
  `completions_mono` (fewer completions below) and `lutK_eq_t_iff` /
  `lutK_eq_f_iff`.
* `lutK_sound`: a Boolean vector admitted pin-wise by a K3 vector gives a
  `lutB` value admitted by `lutK`.
* `stepK_mono`: the network's ternary step is monotone in inputs and state.

**(2) Algorithm A.**
* `A_invariant` (the core): if `stepK u s ⊑ s` pointwise, `s` covers the
  initial binary state, and every input is admitted by `u` at every step,
  then `s` covers EVERY state of the run at every step. No delay bound.
* `stable_old_le`: a state stable for the old inputs `a`, with `a ⊑ u`,
  satisfies the chain condition `s0 ⊑ stepK u s0` (Algorithm A's start).
* `iter_chain`, `iter_above`: from such `s0` the iteration is increasing.
* `algA_sound`: when the iteration reaches a fixed point it covers every run.
* `algA_terminates`: if all nodes `≥ size` are inputs, a fixed point is
  reached within `size + 1` steps. `algA` packages termination + soundness.

**(3) Algorithm B.**
* `algB_stable` (unbounded GMW): every binary stable state (inputs inside the
  final vector `a`, every gate equal to its LUT value on the state) covered by
  the A result is covered by every B iterate. With `A_invariant`: a definite
  node of the A-then-B result has that value in every stable state any run
  can reach.
* `algB_bounded`: under `Bounded D W`, if from `T0` on the inputs are inside
  `a`, every state at step `≥ T0 + m·(D+W+1)` is covered by the m-th B
  iterate from the A state. `algB_settles`: so every definite node of the
  m-th iterate is reached and held by every run from then on.

**(4) Arbiter instance** (7b's network, real INITs: `ustate` O6/O5,
`ugrant` O5/O6, two `bd_c2`; nodes 0 r1, 1 r2, 2 A0@ustate, 3 A0@acks, 4 rst,
5 q, 6 g1, 7 g2, 8 R0, 9 A1, 10 A2).
* `stepK_enc`: the generic `stepK arbNet` IS 7b's `step` under the encoding
  (proved by `rfl` per node); `iter_enc`, `iterB_enc` lift `settle`. So the
  7b `decide` computations are reused, not redone.
* `arb_acks_quiet` (unbounded delays): `IdleServer v` (A0 = 0 on both fork
  branches and rst = 0 at all times, A1 = A2 = 0 at time 0) implies A1 = A2 = 0
  at ALL times, for ANY request waveforms and ANY gate/wire delays. (This is
  7b's shared phase-A state `⟨x,x,x,x,f,f⟩` turned into a trace theorem.)
* `arb_runt_opposite` (= `sc_runt_opposite`): IdleServer, requests arbitrary
  until `T0`, then r1 = 0, r2 = 1. Every bounded run has, from
  `T0 + 4·(D+W+1)` on, q = 0, g1 = 0, g2 = 1, R0 = 1, A1 = A2 = 0.
* `arb_tie_rising` (= `sc_tie_rising`): same with r1 = r2 = 1 after `T0`:
  R0 = 1, A1 = A2 = 0 from `T0 + 4·(D+W+1)` on; q/g1/g2 are not determined.
* `arb_runt_opposite_stable`, `arb_tie_rising_stable`: the same conclusions
  for every stable state reachable in the unbounded model.
The bound is 4 B iterates, not 7b's 3, because the generic step reads inputs
from the previous state (one extra step for the final inputs to arrive).

## What did not work / not done

* **Exactness (the converse of B-S's results) is not proved**: that an `x`
  in the A-then-B result means some run really does not settle or settles
  differently. That direction needs a delay node on every wire (B-S's
  "complete network" condition) and an explicit construction of runs; it is
  the harder half and was out of the time box. Consequently `arb_tie_rising`
  says nothing about q/g1/g2 (it does not claim a run exists that grants
  client 2; that follows from 7a's binary analysis, not from here).
* Only soundness for the GMW model with unbounded/bounded delays. Values in
  the binary trace are binary: mid-rail levels and metastability are outside
  this model; they are what the ternary `x` over-approximates only through
  H_KLEENE_LUT (each LUT output is admitted by the closure). A node that
  toggles (e.g. an oscillating or runt-y loop) and so is seen as 0 by one pin
  and 1 by another at the same step IS covered (per-pin read times), but a
  node that sits at a mid-rail level, read differently by different
  thresholds, is not a binary trace at all; that needs the analog model (7c/7d).
* The A0-fork scenarios (`sc_a0_fall_*`) and `sc_tie_acked` were not lifted;
  they lift the same way (`iterB_enc` and a multi-phase chaining of
  `A_invariant` / `algB_bounded`), about 1 h each; a generic multi-phase
  lemma (run a list of phases, each phase's result as the next phase's A
  start) would make it mechanical.
* `IdleServer` asks for A1 = A2 = 0 only at time 0: the theorems are for any
  initial q/g/R0 values, not just `own1`/`idle1` (stronger than 7b's
  scenarios).

## Verdict

**Works.** (1), (2) and the soundness half of (3) are fully proved for a
general LUT network in a GMW model with per-pin unbounded wire delays (and
with bounds D, W for convergence), and H_TERNARY_SIM (soundness direction)
is discharged for 7b: three scenario-level trace theorems about the arbiter
(`arb_acks_quiet`, `arb_runt_opposite`, `arb_tie_rising`, plus stable-state
versions) hold for ALL binary traces. Effort to finish: exactness (converse)
2-3 days; multi-phase lifting lemma + remaining 7b scenarios 0.5 day; porting
to Core's trace type once fixed (time `ℕ` with per-pin read times maps onto a
bounded-pure-delay channel with `D`, `W` in steps) ~0.5 day. What it buys:
every ternary computation on the cell library (7b, and any future Kleene
scenario) becomes a theorem about every binary trace under every delay
assignment, with a checked convergence time `T0 + m·(D+W+1)`. In particular
the 7b claims "acks never fire while the server is idle, whatever the
requests do" and "after a runt the arbiter settles to the definite winner"
are now proved, not hypothesised.

## Fidelity per primitive

* **LUT (LUT6 / LUT6_2)**: binary `lutB` on the real INIT for the trace, Kleene
  `lutK` (H_KLEENE_LUT, probe Bf: equal to the per-mux Kleene tree in any
  pin order) for the simulator. Hazards inside the mux tree are covered: with
  per-pin read times the output may take the LUT value of any mixture of
  recent pin values, which contains every transient the per-mux model allows
  (Core `LutTree` soundness). O5 and O6 are separate gate nodes with
  independent pin reads (over-approximation; on silicon they share input
  buffers). Mid-rail output levels are not represented (binary traces).
* **Wires / feedback (q -> I2, C-element q -> I2)**: per-pin read of a past
  value; unbounded (soundness) or ≤ W steps (convergence). Covers pure,
  inertial and non-FIFO behaviour. Fork branches are independent pins, so
  isochronic-fork assumptions are never made (A0's two fork branches are also
  separate nodes, as in 7b).
* **Gate delay**: GMW (each gate may hold arbitrarily long; with H_GATE_BOUND
  at most D+1 steps once its LUT value is steady).
* **Tied pins**: `Src.const`, clean rails.
* **Time**: discrete steps; any finite real delay assignment with a common
  resolution maps onto it (steps finer than the smallest delay difference).
