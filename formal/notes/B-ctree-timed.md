# B probe 5f: timing of `bd_c3`, `bd_c4` and `bd_ctree`

File: `formal/lean/Formal/Cells/CTreeTimed.lean` (about 1450 lines, core Lean
only). It imports `Formal.Cells.CElemTiming` (5b) and `Formal.Cells.CTree`
(5c), read-only. Nothing is in `Wip/`.

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/CTreeTimed.lean

Status:
- The file checks clean: no output, no warnings, no `sorry`/`admit`/`axiom`/`native_decide`.
- It takes about 25 s, not the 1 s of the other core files. Most of that is
  `omega` on the 4-child cases with nested `max`/`min`. That is harmless, but
  it is the place to optimise if it matters.
- I ran `#print axioms` on all 35 main theorems from a scratch copy. 26
  depend on `[propext, Quot.sound]`, 4 on `[propext]` only, and 5 on
  `[propext, Classical.choice, Quot.sound]` (the four-phase theorems, through
  `Classical.em`/`byContradiction`).

## Part 1: `bd_c3` / `bd_c4` (5b's results with their real pin maps)

### The generic loop

5b's `exc_held` was tied to `bd_c2`'s pin map, with feedback on I2.
`LoopG F O qp dlmin dlmax dwmin dwmax` takes the LUT function as an arbitrary
`F t q`: the INIT evaluated on the non-feedback pins at `t`, with `q` on the
feedback pin. Its fields are the same named hypotheses as in 5b:
- `H_LUT`: the LUT delay is a window channel `[dlmin, dlmax]`.
- `H_FB`: the feedback wire is a window channel `[dwmin, dwmax]`.
- `H_LOOP_POS`: the loop delay is positive.

Theorems:
- `exc_heldG`, `O_heldG`, `qp_heldG`: forced, then held, for any pin map.
  The end of the hold window is exclusive here.
- `loopG_of_loop`: 5b's `Loop` is an instance of `LoopG`.

### The INITs

`c2r_ce`, `c3r_ce`, `c4r_ce` (by `decide` over the real INIT, through 5c's
`c2r/c3r/c4r` = `lutB INIT [pins]`) show that each cell's function is
`~rst . celem(inputs, q)`. The pin maps are:
- `bd_c3`: `I0..I2` = inputs, `I3` = q, `I4` = rst.
- `bd_c4`: `I0..I3` = inputs, `I4` = q, `I5` = rst.

### Theorems for any fan-in (list of inputs)

- `ce_follow_hold`:
  - `H_PULSE`: all inputs equal `v` and `rst = 0` for `Dmax` ticks.
  - `H_NORST`.
  - `H_SOME`: some input equals `v`.
  - Then `O = v` on `[t0+dlmax, t2+dlmin]` and `qp = v` on `[t0+Dmax, t2+Dmin]`.
- `ce_reset`: a reset pulse of `Dmax` ticks, then at least one input is 0,
  gives 0 throughout.
- `ce_four_phase`: 5b's `c2_four_phase` with lists. It has the same
  hypotheses, including `H_ENV_LATENCY : dlmax + dwmax ≤ dlmin + E`.

### Instances with the real cells

- `c3_follow_hold`, `c4_follow_hold`, `c3_reset`, `c4_reset`,
  `c3_four_phase`, `c4_four_phase`, stated on `F3`/`F4` (the real INIT and
  pin map).
- `c3_runt`, `c4_runt`: tightness of `Dmax` for `bd_c3`/`bd_c4`.
  - With the other inputs tied to 1 and `rst = 0`, `bd_c3`/`bd_c4` compute
    `b || q` (`c3_as_c2`, `c4_as_c2`, by `decide`), the same as `bd_c2` with
    `a = 1`.
  - So 5b's closed-form runt traces satisfy the real `bd_c3`/`bd_c4` gate
    relations (`LoopG`, fixed delays `dl`, `dw`).
  - The inputs are constant after `t0 + w`, but `qp` oscillates with period
    `D` for every runt width `0 < w < D`.

## Part 2: the timed tree

### Model

- `S`: a tree of `n2`/`n3`/`n4` nodes (`bd_c2`/`c3`/`c4`) over leaves `a[i]`.
- `ND`, per node:
  - LUT delay `[lmin, lmax]`;
  - own feedback wire `[fmin, fmax]`;
  - output wire to the parent's pin `[wmin, wmax]`.
- A leaf carries its port-wire window.
- `Run rst x s O` (relational gate semantics): there exist traces for every
  child output, child pin and feedback pin such that:
  - each cell satisfies `LoopG` with its real INIT/pin map (`CTree.c2r/c3r/c4r`)
    and its own delays;
  - each edge satisfies `WinDelay`.
- `ofT u : CTree.T → S` puts uniform delay classes on 5c's tree terms, so 5c's
  `gen n` (the generate block) is reused directly.

### Environment hypotheses (named)

- `H_LEAF`: clean four-phase leaves at the ports. Leaf `i` is `V k` on
  `[σ i k, σ i (k+1))`.
- `H_LEAF_MONO`: `σ i k ≤ σ i (k+1)`.
- `H_ALT`: the phase targets alternate.
- `H_ACK`: for every leaf and phase there is a `u ≥ c k` (`c k = cT σ s k` =
  the last leaf arrival) with `O_root u = V k` and `u + E ≤ σ i (k+1)`.
- `H_NORST`, `H_START`: `rst = 0` from `T0`.
- `H_RESET_DONE`, at the root only: the root reads `!V 0` on
  `[c 0, Early root 0)`. Internal nodes need no reset assumption: they are
  forced by their inputs, and `exc_heldG` does not depend on the prior state.

### Timing quantities (max-plus, exact per phase)

- `Late n k = lmax n + max_j (Late j k + wmax j)` (leaf: `σ i k`). This is
  when node `n` has certainly settled to `V k`.
- `Early n k = lmin n + max_j (Early j k + wmin j)`. This is the earliest time
  `n` can move to `V k`. A C-element moves only after ALL its inputs have, so
  this is a max, not a min.

### Theorems

- `node_step`: one node in one phase, for any list of input pins.
  - Hypotheses: every pin is `v` on `[lo j, hi j)`, and
    `max lo + lmax + fmax ≤ hi j` for every `j`.
  - Conclusion: `O = v` on `[max lo + lmax, max hi + lmin)`.
- `tree_phase`: under `PhaseHyp`, which includes `NodesOK σ k B s`, every
  node drives `V k` on `[Late n k, Early n (k+1))`. Proved by structural
  induction on `S`.
  - `NodesOK σ k B s`: for every node, `Late n k + fmax n ≤ B`.
  - `B`: the earliest time any leaf leaves `V k`.
- `tree_four_phase`: under the per-phase lifted fork condition
  `H_ENV_LATENCY : ∀ k, NodesOK σ k (Early σ s k + E) s`, the root output
  is `V k` on `[Late s k, Early s (k+1))` for every phase `k`. The proof is
  an induction over phases. The ack argument forces `u ≥ Early root k`,
  hence `B = Early root k + E`.
- `tree_four_phase_static`: the same, under a phase-independent condition.
  - `H_ENV_STATIC : StaticOK E 0 s` requires, for every node `n`,
    `Spread n + fmax n ≤ dist_min(n → root) + E`.
  - `Spread n = (lmax-lmin) + max_j (Spread j + (wmax j - wmin j))`.
  - `dist_min(n → root)`: the sum of `lmin + wmin` from `n` up to the root.
  - Conclusion: the root is `V k` on `[c k + Lmax s, Early s (k+1))`.
  - `static_ok` lifts the static condition to `NodesOK`, through
    `Late_le_Early : Late ≤ Early + Spread`.
  - For a single cell with zero port wires, the condition reduces to 5b's
    `E ≥ fmax + (lmax - lmin)`.
- `Late_le`: `Late s k ≤ c k + Lmax s`.
  - `Lmax` = max over leaf-to-root paths of `Σ (lmax + wmax)`, including the
    port wire. This is the bundling-budget term.
- `Early_ge`: `c k + MinD s ≤ Early s k`, with `MinD` = min over paths of
  `Σ (lmin + wmin)`. This is the hold-side term.
- `Lmax_depth`: for uniform delays and any 5c tree,
  `Lmax + wmax_out ≤ depth · (lmax + wmax) + imax`. For a cell-rooted tree
  that is `Lmax ≤ depth·lmax + (depth-1)·wmax + imax`.

### Instances with symbolic uniform delays

Delay classes `U`: LUT `l`, feedback `f`, inter-cell wire `w`, port wire `i`.

| | N = 5, `gen 5` = `C2(C4(a0..a3), a4)` | N = 8, `gen 8` = `C2(C4, C4)` |
|---|---|---|
| depth | 2 | 2 |
| `Lmax` | `2 lmax + wmax + imax` (`gen5_lat`) | `2 lmax + wmax + imax` (`gen8_lat`) |
| `MinD` bound | `lmin + imin`: a4 goes straight to the root (`gen5_early`) | `2 lmin + wmin + imin` (`gen8_early`) |
| Environment condition | `fmax + 2(lmax-lmin) + (wmax-wmin) + (imax-imin) ≤ E` (`gen5_static`) | same (`gen8_static`) |
| Main theorem | `ctree5_timed` | `ctree8_timed` |

In both cases the root's condition implies the C4 nodes' conditions.

The main theorems state: output `= V k` on `[c k + 2lmax + wmax + imax, c(k+1) + L)`,
where `L` is the `MinD` bound for that shape.

## Findings

1. **The bundling term.**
   - The tree's output follows the last input within
     `Lmax = max over paths of Σ(lmax + wmax)`.
   - With uniform delays this is `depth·(lmax+wmax) - wmax + imax`.
   - For N = 5..16 (depth 2) it is `2 lmax + wmax + imax`.
   - The bound in the main theorems is per phase and exact in the
     max-plus sense (`Late`). `Lmax` is its static upper bound.
2. **The lifted fork condition is about accumulated delay SPREAD, not latency.**
   - Requirement: `fmax_n + Spread_n ≤ dist_min(n → root) + E` for every
     node `n`.
   - For N = 5 or 8 with uniform classes:
     `E ≥ fmax + 2(lmax - lmin) + (wmax - wmin) + (imax - imin)`.
   - The spread grows with depth. `E` is measured from the root's ack to the
     next move of any leaf. The feedback of the root and of every internal
     node must have settled within that time.
   - A first version of this probe used `lmin_root` as the lower latency. It
     demanded `E ≥ 2lmax + wmax + imax + fmax - lmin`, which is probably
     impossible to meet. The max-plus `Early` removes that. The final
     condition is the one to put into track 10's checker: per tree node,
     routed `fmax` plus the accumulated min/max spread below it, against the
     minimum environment loop delay.
3. **No internal-node reset is needed for timing.** Only the root's initial
   value enters, through the ack argument. Physically every node is reset
   anyway.
4. **The `Dmax` minimum pulse width is exact for `bd_c3`/`bd_c4` too**
   (`c3_runt`, `c4_runt`).

## Not done / unproved

- **Necessity of the tree fork condition.** It is not proved. Only the
  per-cell `Dmax` tightness is proved. A counter-trace showing that a tree
  violating `StaticOK` oscillates or latches wrong would be the negative
  control. Expected effort: half a day, adapting 5b's runt construction.
- **Non-vacuity of `Run` plus the hypotheses.** No concrete tree run is
  constructed. The hypotheses are physically natural, but I did not build a
  witness.
- **Leaves must switch cleanly** (`H_LEAF`). 5b's single-cell theorem allowed
  inputs that chatter while one input holds. The tree theorem does not.
  Internal glitches are allowed: window channels are non-FIFO, and
  child-output transition windows may glitch.
- **The static condition is sufficient, not exact.** `NodesOK` per phase is
  the exact (max-plus) form used.
- **Lumped LUT delay.** As in 5b, the delay is lumped at the output. Per-pin
  I→O delays are not covered; on the input side they could be folded into
  the edge windows.
- **Generic widths.** Only N = 5 and N = 8 are instantiated. `Lmax_depth`
  covers every shape, but `depth (gen n)` is not computed symbolically for
  all n.
- **Internal feedback pins.** `qp` claims for internal nodes are not
  exported. Only `O` claims are.
- **Inertial and involution channels, Kleene X.** Not covered here (see 5b
  and 5a).

## Verdict

Works.
- Goal (1) is fully proved, including tightness.
- Goal (2) is fully proved, with exact per-phase max-plus windows and a
  static spread-based condition.
- Goal (3) is proved for N = 5 and N = 8 with symbolic uniform delays.

The work took about 2 h. Finishing the necessity counter-trace and a
non-vacuity witness would take about 1 day.

What it buys the project:
- the depth term for the bundling budget, `Σ (lmax + wmax)` over the
  critical path;
- a concrete, checkable timing rule for every `bd_ctree` node:
  `fmax + accumulated (max - min) spread ≤ min delay to the root + E`.
  This rule is not in the library's rules today.

## Fidelity per primitive

- **LUT6 cells (`bd_c2`/`c3`/`c4`).**
  - Real INIT constants and pin maps, through `lutB`. Binary values only.
  - Delay is a window `[lmin, lmax]`, lumped at the output, non-FIFO
    (glitches inside transition windows are allowed).
  - Not a pass-transistor mux-tree model. No X, no runt shaping.
- **Feedback wire.** A routed net with window `[fmin, fmax]`. No R/C, no
  pulse degradation.
- **Inter-cell and port wires.** Window channels `[wmin, wmax]` per edge, one
  window per edge. Pip-level behaviour is not modelled.
- **Environment.** Abstract four-phase hypotheses on traces, not composed
  cells.
