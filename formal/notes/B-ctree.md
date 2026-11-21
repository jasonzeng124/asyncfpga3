# B-ctree: probe 5c, `bd_ctree` (C-element tree vs. flat N-input C-element)

File: `formal/lean/Formal/Cells/CTree.lean` (core Lean, imports only
`Formal.Cells.Prelim`, about 2 s to check). Nothing in `Wip/`.

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/CTree.lean

It checks clean: no output, no `sorry`/`admit`/`axiom`/`native_decide`.
`#print axioms` on every main theorem shows only `propext` and `Quot.sound`
(I ran it from a scratch copy, so the file has no `#print` lines).

## Verdict

**Works.** Both claims in the `bd_ctree` header are proved with the real
INITs, in a speed-independent interleaving model with atomic cells
(H_ATOMIC_CELL). Scope (audit REPORT row 21, findings B #5): "tree = flat
C-element" means EQUALITY OF REACHABLE (phase, inputs, output) STATE SETS in
this atomic-cell model (plus the step simulations below), not equality of
traces and not a timed statement:
- the concrete counterexamples;
- the equivalence under the four-phase discipline, **for every tree shape** by
  structural induction. The fallback (finite `decide` for N=5) was not needed.
  Each generate-block width from 2 to 64 is a corollary.

Effort to finish: none for what was asked. The open part is the link down to
timing (see "What is not proved"), about 1-2 days if combined with probe 5b's
bounded-delay C-element result.

What it buys the project:
- The header's "verified by exhaustive search over interleavings in
  tb_prims" becomes a proof for all shapes and widths.
- It pins down which part of the discipline matters. It is the wait for the
  acknowledge. "Fundamental mode" (internal nodes settle before the next input
  change) is not needed.
- It adds a persistence result. That is the hook for a later bounded-delay or
  Kleene refinement.

## Model

- **State:** the input vector `Nat -> Bool` plus the output bit of every cell,
  stored in the tree term `T` itself.
- **`T` constructors:**
  - `leaf i` is input `a[i]`. A chunk of one input is `assign q = a[0]` in
    the RTL, so it is a leaf.
  - `n2`/`n3`/`n4` are `bd_c2`/`bd_c3`/`bd_c4`.
  - `wire` is a routed wire with its own unbounded delay: a one-bit buffer.
- **`Fire` (one atomic move):** one cell's output becomes
  `lutB INIT [pins..., own q, rst=0, ...]`, using the cell's real INIT and pin
  map from `bd_ce.v`. The tree recursion is the generate block itself
  (`gen`, chunks of four), checked against the hand trees by `rfl`:
  - `gen 5 = C2(C4(a0..a3), a4)`
  - `gen 8 = C2(C4, C4)`
  - `gen 9 = C3(C4, C4, a8)`
- **Environment (`Disc`):**
  - `fourPhase` (H_FOUR_PHASE): in phase `v` an input may only move to `v`.
    The phase turns only when all leaf inputs are `v` and the tree output is
    `v`.
  - `noAck`: the turn waits for the inputs only.
  - `free`: any input changes at any time.
- **Flat reference (`FStep`):** a single N-input C-element `z` under the same
  environment. It may fire to `b` only when every input is `b`.

### Note on the shape

The generate block does NOT build the header's example. For N=5 it builds
`C2(C4(a0..a3), a4)` (chunks of four), while the header's example is
`C(C(a0,a1), C(a2,a3,a4))`. Both shapes are covered.

## Theorems (all proved)

**Cell lemmas, all by `decide` over the INIT:**
- `c2_eq`, `c3_eq`, `c4_eq`: each INIT (rst=0) equals the C-element
  `celem` (all 1 gives 1, all 0 gives 0, otherwise hold).
- `c2r_rst`, `c3r_rst`, `c4r_rst`: with rst=1 the next value is 0.
- `c*_inv`, `c*_out`, `c*_all`: the per-cell facts used by the induction.

**Part 1: counterexamples (concrete reachable runs, real INITs).**
- `cex_code5`: the generate-block N=5 tree, free environment.
  - Input sequence: `11110`, then the C4 cell fires to 1, then `01110`, then
    `01111`.
  - From that reachable state the top cell can fire and the output rises from
    0 to 1 while the inputs are `0 1 1 1 1`.
  - `flat_rise_needs_all`: a flat C-element can rise only when every input is
    1, so no flat move makes this change. The inputs were never all 1, so the
    flat element held 0 throughout.
- `cex_header5`: the header's example `C(C(a0,a1), C(a2,a3,a4))` with the
  vector `0 1 1 1 1`.
  - Input sequence: `00111` (right cell to 1), `00011`, `11011` (left cell to
    1), `01011`, `01111`; then the top cell rises.
  - Correction to the header's wording: the left sub-tree does not "track a0
    and a1". At `0 1` a C-element holds, so the left cell must also hold a
    stale 1 from an earlier `1 1` on a0, a1. The header's conclusion is still
    right.
- `cex_noAck5`: every input rises once and falls once, but the environment
  turns without waiting for the output.
  - All five inputs rise, the C4 cell fires, the environment turns before the
    top cell fires, and a0..a3 fall.
  - The top cell then rises while the inputs read `0 0 0 0 1` in the falling
    phase.
  - So the ack wait in H_FOUR_PHASE is necessary.

**Part 2: under H_RESET and H_FOUR_PHASE, for every tree `t0` whose root is a
cell (wires anywhere allowed).**
- `reach_inv`: phase invariant `Inv`. In phase `v`, every cell holding `v`
  sees `v` on all its inputs.
- `tree_move_is_flat_move`: every firing anywhere in the tree either leaves
  the output unchanged or sets it to `v` while every leaf input is `v`. That
  is a flat C-element move.
- `reach_mono` / `fire_mono`: in phase `v`, no cell or wire ever moves away
  from `v`. Inputs also only move toward `v` (`Mon`). Consequences:
  - every node switches at most once per phase;
  - an excited cell stays excited until it fires (speed-independent
    persistence);
  - in this model there is no runt and no withdrawn excitation at any node.
- `settled_at_turn`: when the ack arrives (output = `v`), every internal cell
  and wire holds `v`.
- `live`: when all leaf inputs are `v`, cell firings alone reach the state
  where all cells hold `v`. No deadlock, and the tree always catches up with
  the flat element.
- `refines_flat` and `flat_refines`, combined in `reachable_eq_flat`: the
  reachable (phase, inputs, output) states of the tree are exactly the
  reachable states of the flat C-element over `leaves t0`.
  - Forward direction: each tree step is a flat step or a stutter.
  - Backward direction: each flat step is matched by finitely many tree steps.
  - So the observable behaviours match up to stuttering. The trace-level
    statement is not written out as one theorem; it follows from the two
    step simulations.
- Instances:
  - `ctree5_eq_flat` (gen 5) and `ctree8_eq_flat` (gen 8);
  - `header5_eq_flat` (the header's shape);
  - `ctree5_wires_eq_flat` (gen 5 with a delayed wire on every edge);
  - `ctree_eq_flat`: every generate-block width 2..64, via `gen_ok`, checked
    by `decide`. 64 is only how far the enumeration was asked to go.

## Named hypotheses and what the interleaving model hides

**H_RESET** (explicit argument `AllQ false t0`): every cell starts at 0 and
every input at 0.
- Justified by `c*r_rst` (rst=1 forces 0), provided rst is held long enough
  for every cell to fire once.
- Test: GLS reset release, then check every tree node is 0.

**H_FOUR_PHASE** (the `fourPhase` discipline): stated above.
- Test: a protocol monitor on the bd_ctree ports in GLS of the real join/fork
  users.
- `cex_noAck5` shows the ack wait in it cannot be dropped.

**H_ATOMIC_CELL** (the `Fire` relation itself; it is the model, not a Lean
argument). This is the speed-independent / interleaving assumption: each
cell's update is one atomic, clean transition. Physically it stands for two
facts:
1. A LUT's output makes one clean transition, with no glitch, runt or
   intermediate value. The proof helps here: in every reachable state, inputs
   only move toward `v` and no excitation is ever withdrawn (`fire_mono`).
   Each LUT therefore sees only monotone input changes, at most one per pin
   per phase. That is exactly the case covered by the single-input-change
   glitch-freedom lemmas of probes 4/5a under H_KLEENE_LUT.
2. **Isochronic feedback fork.** The cell's output forks to its parent and
   back to its own `q` pin. The model treats both branches as updated
   together. In reality the feedback branch must arrive before that LUT's
   other pins move again. By monotonicity, the next opposite move of those
   pins comes only after a full round trip: this cell, then its ancestors,
   then the root ack, then the environment, then the leaves, then this cell's
   children. So the real condition is that the feedback delay is less than
   that round trip. That is the bounded-delay condition probe 5b derives for a
   single cell, and it is the only timing assumption left.
   - Test: GLS of a routed tree with the feedback pip at slow-max and the
     environment loop at fast-min.

**Interconnect between cells needs no timing assumption.** `wire` nodes on
any edge are covered, because every theorem is for every tree. The only fork
in a tree is each cell's own feedback, which is inside the cell.

**Fundamental mode is NOT assumed.** Inputs may change while internal cells
are still firing within a phase. Settling of the internal nodes before the
turn is a consequence of the ack wait (`settled_at_turn`), not a hypothesis.
The timing assumption the interleaving model hides is H_ATOMIC_CELL item 2
(the isochronic feedback fork), plus unbounded-but-finite cell delays
(liveness only).

## Fidelity per primitive

- **LUT6 cells (`bd_c2`/`c3`/`c4`):**
  - Real INIT constants and pin maps, evaluated with `lutB`; the rst pin is
    tied to 0 after reset.
  - Binary values only. No Kleene X and no mux-tree internals.
  - Atomic update (H_ATOMIC_CELL). This is a speed-independent abstraction of
    the pass-transistor mux tree. It is faithful only given the
    monotone-input result above plus the per-LUT glitch-freedom of probes
    4/5a.
- **Feedback wire:** zero-delay and isochronic with the cell output. This is
  the main gap, closed only by probe 5b's bounded-delay analysis.
- **Inter-cell routing:** arbitrary finite delay, modelled as a one-place
  buffer (`wire`). By persistence a buffer never has two transitions in
  flight, so a one-place buffer is faithful to a pure (transport) delay here.
  Routing glitches and pass-transistor pip behaviour are not modelled.
- **Environment:** an abstract four-phase protocol, not the real join/fork
  cells.

## What did not work / not proved

- Trace-level equivalence is not stated as one theorem; it is implied by the
  two step simulations. What is stated is equality of reachable-state sets
  in the atomic-cell model.
- The generate block is proved for every tree shape, and its widths are
  checked by evaluation for 2..64. There is no symbolic proof that `gen n`
  is a cell rooted, reset-0 tree for all n; it is easy, but the fuelled
  recursion makes it tedious.
- Not connected to a timed or Kleene semantics. The step to bounded delays is
  H_ATOMIC_CELL item 2 and needs probe 5b's result.
- Not a hold-time / runt analysis of the real LUT: monotone inputs are proved
  here, glitch freedom of a LUT under them is probe 4/5a's job.
- No interaction with `rst` during operation.
