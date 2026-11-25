# B probe 7i: multi-phase ternary soundness, the remaining 7b scenarios, exactness witnesses

File: `formal/lean/Formal/Cells/TernaryPhases.lean` (core Lean, ~1080 lines,
imports `Formal.Cells.Prelim`, `Formal.Cells.ArbKleene`,
`Formal.Cells.TernarySound`; none of them edited; no Mathlib). Everything new is
local to this file (`Phase`, `Closed`, `Links`, `Follows`, `Good`, `InputsIn`,
the run constructor `dsim`/`dv`, Boolean info-order helpers `kle`/`nle`/`ile`,
the C-element network `cNet`). Nothing was added to Prelim.

Check (clean, no output, about 4 s):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/TernaryPhases.lean

`#print axioms` (run on a scratch copy) on every main theorem gives
`[propext, Quot.sound]`, plus `Classical.choice` for `dsim_periodic`/`dsim_const`
and the run theorems that use them (`arb_a0_fall_skewed_early_ack`,
`arb_a0_fall_noskew`, `cel_x_exact`, `arb_tie_exact`). There is no sorry, admit,
axiom or native_decide in the file, and `formal/scan.py` passes.

## Model

This is 7f's model, unchanged: discrete time, a binary trace `v k n`, a `Run`
with per-pin read times (H_WIRE_CAUSAL), and GMW gates (H_GMW_GATE: each gate
either holds or takes `lutB` of what its pins see). `Bounded D W` adds
H_WIRE_BOUND (a wire is at most `W` steps old) and H_GATE_BOUND (a gate whose
LUT value is steady for `D+1` steps shows it by then). The arbiter network is
7f's `arbNet`: nodes 0 r1, 1 r2, 2 A0 at `ustate.I4`, 3 A0 at the ack
C-elements, 4 rst, 5 q, 6 g1, 7 g2, 8 R0, 9 A1, 10 A2, with real INITs.

## (1) Generic multi-phase lemma

* `phase_cov` (one phase with a start time): `s` is closed under the window
  step (`stepK u s ⊑ s`). `Entry` means `s` covers the run on the `W+1` steps
  up to the window start `S`. The inputs are inside `u` on `(S, E]` and inside
  `a` on `(F, E]`. Then `s` covers the run on `[S, E]`, and the `m`-th B iterate
  covers it on `[F + m(D+W+1), E]`. The `W` steps before `S` are needed because
  a read at `k > S` can go back up to `W` steps, to before the window opened.
* `phases_sound` (a list of phases, by induction): each phase gives
  `u, a, s, m, S, F`. The conditions are:
  * `Closed`: each `s` is closed for its `u`, and `S ≤ F`.
  * `Links`: each phase's B result is below the next phase's `s`, and
    **`p.F + p.m(D+W+1) + W ≤ q.S`**.
  * `Follows`: the run's inputs follow the phases, each phase lasting until the
    next window start.
  * `Entry` for the first phase.

  The conclusion (`Good`): every phase's A state covers the run from `S` to the
  next window start, and its B result covers it from `ready` to the next window
  start (for the last phase, for ever). The hold time is `m(D+W+1) + W`, not
  `m(D+W+1)` as in the brief. The extra `W` lets every wire flush before the
  next window, and without it the induction does not go through.

## (2) The remaining 7b scenarios as trace theorems

* `arb_tie_acked` (two phases, bounded). Both requests change from 0 and are
  high from `F1`. A0 = 0 on both fork nodes until `S2 ≥ F1 + 4(D+W+1) + W`.
  After that A0 may do anything, and it is high from `F2 ≥ S2`. There is no
  reset and the acks start low. Then **A1 = A2 = 0 up to `S2`, and R0 = 1 from
  `F1 + 4(D+W+1)` on, for ever**, through the server's ack and any A0 waveform.
  q, g1, g2, A1 and A2 after the ack are `x`, so no claim is made about them.
* `arb_runt_held` (one phase, UNBOUNDED delays, `A_invariant`). A0 = 1 on both
  branches, no reset, and q = 1, g2 = 0, A1 = 1, A2 = 0 at time 0. The requests
  may do anything. Then **q = 1, g2 = 0, A1 = 1 and A2 = 0 at every step, for
  every delay assignment.**
* `arb_a0_fall_ordered` (two phases, bounded). **H_A0_FORK is stated as a
  constraint on the two fork nodes' traces**: node 3 (the A0 branch into the
  ack C-elements) is low from `F1`, while node 2 (`ustate.I4`) is still high
  up to `S2 ≥ F1 + 4(D+W+1) + W`. Node 2 is low from `F2`. Client 2 is waiting,
  and the arbiter starts in `done1`. Then **A2 = 0 at EVERY step (no early ack,
  ever)**, and from `F2 + 4(D+W+1)` on q = 0, g1 = 0, g2 = 1, R0 = 1, A1 = A2 = 0.
* `arb_a0_fall_skewed` (soundness half, any fork skew): from `F + 4(D+W+1)` on
  q = 0, g1 = 0, g2 = 1, R0 = 1, A1 = 0. A2 is not determined.
* **`arb_a0_fall_skewed_early_ack`** (the negative statement, a concrete
  run). This is `dsim` with unit gate delay (D = 0) and every wire 0 steps,
  except the A0 branch into `ua2` (gate 10, pin I1), which is 3 steps (W = 3).
  The run starts in `done1` with r1 = 0, r2 = 1 and rst = 0. A0 falls at step 1
  on BOTH fork nodes and stays low for ever, so the server never begins client
  2's transaction. Even so, q falls at step 2, g2 rises at step 3, and **A2 is
  0 at step 3, rises at step 4 and stays 1 for ever**. The theorem also proves
  that the run is `Bounded … 0 3` and that its inputs and initial state are as
  stated. The two fork nodes carry identical traces here, so the skew is all
  in the routed branch. That is why the trace form of H_A0_FORK must budget
  the wire bound (`+ W`).
* `arb_a0_fall_noskew`: the same inputs with all wires 0 steps. A2 = 0 for
  ever and g2 = 1 from step 4. Together with the early-ack run, both values of
  7b's `x` on A2 occur, so that `x` is exact.

## (3) Exactness (Brzozowski–Seger direction), special cases

There is no general theorem yet. These are concrete witness runs for
particular `x` results.

* **C-element in hold with a runt.** `cNet` is the real `bd_c2` INIT
  (a, b, own output, rst).
  * `cel_ternary`: q = 0, a = 1, b = 0 is stable. Algorithm A with b = `x`
    reaches q = `x` in 2 Jacobi steps and stays there (a fixed point). Every
    Algorithm B iterate with b = 0 keeps q = `x`.
  * `cel_runs_follow`: any b-waveform that is 0 from step 3 gives a run with
    D = 0 and W = 1 (the feedback wire takes 1 step). The run starts at q = 0
    and follows both input phases.
  * **`cel_x_exact`**:
    * no runt: q = 0 for ever;
    * a 2-step runt: q = 1 from step 2 for ever;
    * a 1-step runt: **q oscillates for ever with period 2**, because the pulse
      circulates in the feedback loop.

  So the `x` is reachable both as "settles differently" and as "does not
  settle", under bounded delays.
* **The arbiter's tie** (`tie_runs_ok`, `arb_tie_exact`). The run starts from
  `idle1` with the server idle and no reset. Only the q feedback wire takes a
  step (W = 1, D = 0). All three runs satisfy `arb_tie_rising`'s hypotheses
  (T0 = 3), and R0 = 1 in each, as that theorem says.
  * r1 rises one step before r2: client 1 wins for ever.
  * r2 rises two steps before r1: client 2 wins for ever.
  * **r2 rises one step before r1: q oscillates for ever, and the grants
    alternate.** g1 is high at even steps and g2 at odd steps, never both at
    once. This is the bounded-delay binary shadow of metastability.

Caveat for both oscillating runs: they need a transport (pure) feedback wire
that can carry a one-step pulse. With an inertial wire that filters pulses
shorter than its delay, they would not exist. In that case the exactness
witnesses would be only the two runs that settle differently. Which model the
fabric's routed feedback follows is a fidelity question, and the analog layer
(7c/7d) is where the loop's true behaviour gets decided.

## Run construction (generic, reusable)

* `dsim N dl inp c0` is a unit-gate-delay binary simulation. Pin `p` of gate
  `j` reads `dl j p` steps late. The state is kept as a history list, so the
  definition is structurally recursive and kernel `decide` can evaluate it.
* `dsim_run`: it is a `Run` with read times `k - dl j p`.
* `dsim_bounded`: it satisfies `Bounded … 0 W` whenever every `dl ≤ W`.
* `dsim_periodic` / `dsim_const`: if the inputs are periodic and every gate
  node repeats over a window of `W + 1` steps (checked by `decide`), the run
  is periodic or constant for ever.

## What did not work / not done

* **General exactness is not proved**: "with a delay element on every wire,
  every `x` in the A-then-B result is witnessed by some run". Only concrete
  witnesses exist (C-element, tie, A0-fall). A general proof needs B–S's
  construction: for each `x` node, pick per-wire delays that realise a
  "late" or "early" path. That is a much bigger job, estimated at 2–3 days.
* The tie-acked `x` on A1/A2 (both acks latching `x`) has no witness run yet.
  It would combine the tie oscillation with an A0 rise. It is mechanical
  with `dsim`, about 1 h.
* `arb_runt_held` covers only the window, because 7b has no final phase for
  this scenario. Adding one is mechanical.
* The `+ W` in the phase spacing (see (1)) is stronger than the brief's
  `m(D+W+1)`. It is needed in this model.

## Verdict

**Works.** The multi-phase lemma is proved for general LUT networks. All the
remaining 7b scenarios are now theorems about every binary trace, bounded or
unbounded as stated:
* the tie with the server's ack;
* the runt under hold;
* the A0 fall with H_A0_FORK as an explicit trace constraint;
* the A0 fall with an unconstrained fork.

The skewed A0 fall also has a concrete bounded early-ack run. Exactness is
proved for three concrete `x` results (C-element runt, arbiter tie, A2 under
fork skew). Each has explicit bounded runs, including runs that never settle.

What it buys:
* **The early-ack defect is now a theorem**: a 3-gate-delay lag on the A0
  branch into `ua2` produces an ack that is never matched. With the ordered
  theorem, this pins H_A0_FORK down as a trace condition with the wire budget.
* **"The loop may not settle" is a theorem about bounded runs**, both for the
  C-element and for the arbiter tie.

Remaining effort: general B–S exactness 2–3 days; the tie-acked witness 1 h.

## Fidelity per primitive

* **LUT (LUT6 / LUT6_2)**: `lutB` on the real INITs (`ST_INIT`, `GR_INIT`,
  `C2_INIT`) for traces and `lutK` (H_KLEENE_LUT) for the ternary side. O5 and
  O6 are separate gate nodes, as in 7f, which over-approximates in the
  soundness theorems. In the witness runs every gate is unit-delay with a
  binary output: the runs are physically possible only if the fabric can
  realise these delay ratios. Mid-rail levels are not represented.
* **Wires / feedback**: per-pin delays. They are unbounded or bounded by `W`
  in the soundness theorems, and fixed transport delays in the witness runs
  (A0 to `ua2`: 3 steps; q and C-element feedback: 1 step). Pure delay passes
  one-step pulses. An inertial wire would not, and only the oscillating
  witnesses depend on this.
* **Fork (A0)**: two input nodes (2, 3). H_A0_FORK is a trace constraint on
  them plus the `+ W` budget. The early-ack run shows that branch wire skew
  alone, with identical fork-node traces, breaks the property.
* **Gate delay**: GMW (soundness). In the witness runs it is unit delay, which
  satisfies H_GATE_BOUND with D = 0.
* **Tied pins**: constants (clean rails).
