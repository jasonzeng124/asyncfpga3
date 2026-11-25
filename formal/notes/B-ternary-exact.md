# B probe 7l: exactness of two-phase ternary simulation (Algorithms A and B)

File: `formal/lean/Formal/Cells/TernaryExact.lean`. It is core Lean, about 1100
lines, and imports `Formal.Cells.Prelim`, `Formal.Cells.TernarySound` and
`Formal.Cells.TernaryPhases` (7i's `cNet`, used only for the instance). None
of the imported files was edited, and nothing was added to Prelim. Everything
new is local to this file:
* `kval`, `inw`, `sig`, `wv`, `tv`, `sA`, `fv`, `Tog`;
* the converse completion lemmas.

Check (clean, no output, about 4 s):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/TernaryExact.lean

`#print axioms` was run on a scratch copy for every main theorem below. Each
gives `[propext, Quot.sound]`, plus `Classical.choice` for the run
constructions (read times are picked with `Classical.choose`) and the
iff theorems. There is no sorry, admit, axiom, native_decide or bv_decide in
the file, and `formal/scan.py` passes.

## Result in one paragraph

The general theorem is proved, for arbitrary (cyclic) LUT networks. It is
proved in the delay model that 7f proved soundness for: GMW gates, a per-pin
wire read time (H_WIRE_CAUSAL), and the bounds H_WIRE_BOUND / H_GATE_BOUND
for settling. In that model, ternary simulation is now exactly characterised:
* a gate is `x` in Algorithm A's result **iff** some run changes it;
* a gate is `x` in the A-then-B result **iff** some bounded run never
  settles on it. Every definite node settles in every bounded run (7f).

The acyclic case (Eichelberger) is a special case and needed no separate
proof.

The witnesses do not use per-wire constant delays in every respect:
* For **A**, a witness with constant transport delays exists.
* For **B**, there are two witnesses, each needing one liberty:
  * a clean input edge, but non-FIFO reads;
  * FIFO wires of delay 0 or 1, but glitching inputs.

A single witness with all of clean input edges, FIFO wires and bounded gates
is open.

## Setting (hypotheses of every exactness theorem)

* `hstab`: `c0` is a stable binary state. Every gate equals `lutB` of its INIT
  on `c0`'s pin values. This is what "the circuit was at rest" means.
* `hu`: the A input vector `u` admits both `c0` and the final inputs `a'` on
  every input.
  * `u = c0 ⊔ a'` is B–S's single input change. The witness inputs then make
    one clean edge (`inw_clean`).
  * `u = x` on an input that ends where it started allows a glitch (a runt).
* `hfixA`: the A iteration from `s0 c0` is fixed at `mA`.
* `hfixB`: the B iteration from A's result, with inputs `fin a'`, is fixed at
  `mB`. 7f's `algA_terminates` guarantees `hfixA` for finite networks.
  Termination of B (a decreasing chain from A's fixed point) follows by the
  same counting argument, but it is NOT proved here: `hfixB` is a hypothesis.
  On the instance it is checked by `decide`.

## Theorems (namespace `Formal.Cells.TernaryExact`)

**LUT level**
* `exists_completion`: every value admitted by `lutK init zs` is `lutB` of
  some completion of `zs`. This is the converse of 7f's `lutK_sound`, so the
  Kleene LUT is exact on its own.
* `forall2_of_mem_completions`: a completion is admitted pin by pin.
* `reads_exist`: suppose every value a pin's source may take, under a
  ternary state, occurs in the trace at an allowed time. Then any completion
  can be read with per-pin read times that are all allowed.

**Witness 1, `wv` (bounded, clean edge, non-FIFO)**
* `exact_run`: `wv` is a `Run` with `Bounded … 0 W` for every
  `W ≥ 2·mA + 2`.
  * Gates are unit delay.
  * `σ` (= `sig`) is A's iterates followed by B's iterates. Each ternary step
    is stretched over two time steps.
  * A node that is `x` in `σ (t/2)` shows the parity of `t`.
  * The inputs follow `inw`: old value at 0, final value from 2, and at step
    1 the opposite of the old value if `u` marks the input `x`.
* `A_witness`: a gate that is `x` in A's `k`-th iterate shows 0 at step `2k`
  and 1 at step `2k+1`.
* `B_witness`: from step `2(mA+mB)` on, each gate shows its B value. Where
  that value is `x`, it shows the step's parity, so it oscillates for ever.
* **`A_exact`**: `iter u mA (s0 c0) n = x` ⟺ some bounded run changes `n`.
  The run starts in `c0`, keeps its inputs inside `u`, and has them final
  from step 2.
* **`A_change_sound`**: the `⟸` direction for ANY run, unbounded. A node that
  is definite in A never moves.
* **`B_exact`**: (A-then-B result at `n`) `= x` ⟺ some bounded run (same
  input conditions) never settles on `n`. Here "never settles" means
  `∀ T b, ∃ t ≥ T, v t n ≠ b`. The `⟸` direction is 7f's `algB_settles`,
  with settling time `2 + mB(D+W+1)` in every bounded run.

**Witness 2, `fv` (constant per-wire transport delays, clean edge, A only)**
* **`A_exact_fixed`**: there is ONE run in which every A-`x` gate changes
  value. In this run:
  * every wire `(j, p)` has a constant delay, with read time `k - d j p` and
    the initial value before that;
  * gates are GMW;
  * the inputs follow `inw` (a clean edge at step 1 when `u = c0 ⊔ a'`).

  Each gate toggles once, at the A step where it first becomes `x`, and then
  holds. Two facts make this work:
  * the toggle step is unique (`tog_unique`, because A is an increasing
    chain);
  * one delay per pin, chosen for that step (`tog_delays`), therefore serves
    for ever.

  Gates must be able to hold indefinitely, so this run is not `Bounded`.

**Witness 3, `tv` (FIFO, `D = 0`, `W = 1`)**
* `tv_run`: `σ` advances one step per time step, and a node that is `x` in
  `σ t` toggles at `t`. An `x` source then shows both values in `{t-1, t}`,
  so every read time is `t-1` or `t`. The read times of one pin are
  therefore non-decreasing: FIFO, with no reordering on any wire.
  `Bounded … 0 1` holds.
* `tv_inputs_ok`: the inputs stay inside `u` and are final from `mA + 1`.
  A `u`-`x` input toggles at every step up to `mA`.
* **`B_exact_fifo`**: the B iff with the RHS strengthened to: `D = 0`,
  `W = 1`, FIFO reads, and inputs final from some `T0`.
* `A_witness_fifo`: in `tv`, a gate that is `x` in A's iterate `k + 1` toggles
  at step `k + 1`.

**Instance (non-vacuity)**
* `cel_runt_never_settles`, `cel_runt_never_settles_fifo`. The circuit is 7i's
  `cNet` (`bd_c2`, real `C2_INIT`; inputs a, b, rst, gate q fed back to I2).
  It starts in hold: q = 0, a = 1, b = 0. The b input may glitch (`u` = `x`
  on b) and ends at 0.
  * Computed by `decide`: A is fixed at 2, B is fixed at 1, and q is `x`.
  * The general theorem then gives bounded runs, including a FIFO one with
    `W = 1`, in which q never settles. 7i found such runs by hand; here they
    follow from the general theorem, so its hypotheses are satisfiable on a
    real cell.

## Proof idea

B–S choose delays per wire so that a given X-path is realised. In the
per-pin-read model this choice becomes a choice of read time per pin and
per step. Three steps:
1. `exists_completion`: an `x` (or any admitted value) at a gate is produced
   by some Boolean completion of its pins' ternary values.
2. Make every value that the ternary state admits for a source visible in the
   trace within the read window. Definite nodes show their value. `x` nodes
   show both values:
   * by parity (stretched, `wv`);
   * by toggling (`tv`);
   * or by holding the old value at time 0 and the new value from the toggle
     on (`fv`).
3. `reads_exist` assembles per-pin read times, and `Classical.choose` turns
   them into the `Run` structure.

The stretched construction needs no monotonicity of `σ`. The toggling
construction does not need it either. Both work verbatim for the
non-monotone concatenation "A then B", which is why B costs no more than A.

## What did not work / open

* **One witness with clean input edges, FIFO wires and bounded gates, for
  B.** Each of the two witnesses gives up one property:
  * `wv` keeps clean edges but reads non-FIFO: an inverted dependency inside
    one 2-step block needs a 1-then-0 read from a 0-then-1 source.
  * `tv` is FIFO but toggles the `x` inputs: a gate that must alternate
    needs to see an alternating input, and under FIFO a clean edge is seen as
    at most one change per pin.

  Making B-S's statement fully faithful needs a "bridge" construction: run
  A as in `fv` (constant delays, clean edge), then start the B oscillation
  while slow pins still read old values (FIFO lets a pin lag, then catch up).
  This was not attempted. Effort: about 1–2 days.

  There is a fixed-delay obstruction, analysed but not formalised. With
  CONSTANT per-wire delays, a gate's reads at its two toggle instants are
  rigidly coupled by the distance between those instants. So uniform period
  schedules cannot realise every pin pattern. A (1,1) pin wants a long
  1-interval and a (0,0) pin a short one. B–S avoid this because their wire
  elements are nondeterministic. Expect B to be **not** exact for fixed
  transport delays with unit gates: such a run is deterministic and may
  simply settle.
* **Inertial wires.** Every B witness needs an `x` node to toggle with a
  1-step period: in `wv`, 1-step pulses; in `tv`, toggling every step. A wire
  that swallows pulses shorter than its delay rules these runs out. In that
  model ternary B is sound but only an over-approximation. 7i made the same
  observation about its oscillating witnesses. Which behaviour routed
  feedback on the xc7z010 has is a fidelity question for the GLS or the
  board, not for this file.
* No B–S "outcome" (non-transient-cycle) semantics was formalised. Exactness
  is stated directly as "never settles in some bounded run" versus "settles
  in every bounded run", which is the form 7f's soundness already uses.
* `fv` (`A_exact_fixed`) is not `Bounded`: gates hold their new value
  against later excitations. A bounded constant-delay witness for A was not
  attempted.

## Verdict

**Works.** The general theorem asked for (B–S Ch. 7 exactness of A and of
A-then-B) is proved for arbitrary LUT networks with feedback, in exactly the
model 7f proved soundness for. Ternary simulation is therefore now an exact
characterisation of that model in both directions: no `x` is spurious
relative to it. A is also exact under constant per-wire transport delays.
For B, a FIFO witness with wire delays of 0 or 1 exists if inputs may glitch
within `u`.

To finish the fully faithful B–S version (clean edge, FIFO, bounded): 1–2
days, via the bridge construction above.

What it buys: when a ternary run of a cell, or of the arbiter, reports `x`,
that `x` is now known to be real in the model. Some delay assignment inside
the stated bounds makes the node change (A) or keep moving for ever (B). The
remaining gap between an `x` and silicon is therefore exactly the gap
between the model and silicon:
* inertial filtering;
* FIFO and constant routing delays;
* mid-rail levels and metastability.

That gap is where the GLS and board work should aim. The model's ternary
answers no longer need to be second-guessed.

## Fidelity per primitive

* **LUT (LUT6 / LUT6_2)**: `lutB` on the real INIT for traces, and `lutK`
  (H_KLEENE_LUT) for the ternary side, as in 7f. `exists_completion` shows
  that `lutK` adds no spurious `x` of its own: every admitted value is the
  LUT of some pin mixture. Whether the silicon mux tree can produce every
  such mixture as a transient is the per-pin-read assumption, H_WIRE_CAUSAL
  plus H_GMW_GATE. O5 and O6 would be separate gate nodes, as in 7f; the
  instance here uses only the single-output `bd_c2`.
* **Wires / feedback**: the witnesses use
  * per-pin read times in `[t-2, t]`, plus long reads of the old input
    value, for `wv`;
  * constant transport delays for `fv`;
  * FIFO reads in `{t-1, t}` for `tv`.

  Feedback wires are ordinary pins, and nothing assumes acyclicity. All the
  B witnesses carry 1-step pulses, so they assume transport rather than
  inertial behaviour (see "open").
* **Gate delay**: unit delay for `wv` and `tv` (`D = 0`), GMW with
  unbounded holds for `fv`.
* **Inputs**: `wv` and `fv` give a clean edge at step 1 when
  `u = c0 ⊔ a'`, and a 1-step runt where `u` marks an unchanged input `x`.
  `tv` gives a glitch train inside `u` up to step `mA`, and the final value
  after that.
* **Tied pins**: constants (clean rails).
* **Time**: discrete steps, as in 7f.
