# B-ctree-exact: exact per-node own-loop condition of bd_ctree, any shape

Probe Bct (shard B), 2026-10-27. New file (core Lean only):
`formal/lean/Formal/Cells/CTreeExact.lean`. JSON draft (JSON untouched):
`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Bct/draft_constraints.json`.
No route, board or toolchain run. Follow-up of Bmg (B-necessity-merge.md, finding 3).

## Verdict

Bmg's proposed formula is right, for every tree shape and depth (every node
has fan-in >= 2). The exact condition in the per-pin box, **H_CTREE_LOOP**,
says: for every node `n` and every child `c` of `n`,

    Qhi(n) <= dist_min(n -> root) + E + MaxMin(c) + lo(c -> n)

with
- `Qhi(n)` = n's loop: feedback wire hi + feedback site pin hi + feedback-pin arc hi;
- `lo(c -> n)` = the read of edge c -> n: wire + n's site pin + n's arc from that pin, all lo;
- `dist_min(n -> root)` = the sum of the read lo's on the edges from n up to the root (0 at the root);
- `MaxMin(leaf) = 0`, and `MaxMin(m) = max over m's children j of (MaxMin(j) + lo(j -> m))`;
- `E` = the minimum time from the root's output edge to a leaf's next edge at its port.

No hi bound of any edge enters, and no path spread enters. The old row
`bd_ctree.node_fork` charges the spread of every leaf -> n path. It implies the
new condition (`old_imply_new`), but it is not necessary.

**Why.** Every next-phase edge at n's pins comes after the root has fired. The
root fires no earlier than `n`'s edge + `dist_min`. Every leaf then waits `E`.
A C-element child moves only after its LATEST input, so its earliest next edge
is a MAX of the minimum path delays, which is `MaxMin`. The spread cancels,
because both sides are measured from n's own output edge.

The gcd_hw shapes:
- bd_fork has N = 2..6 and bd_join has N = 2 (B-gcd-cells.md). This gives one node for N <= 4, `C2(C4, wire)` for N = 5 and `C2(C4, C2)` for N = 6.
- With a uniform read lo `l`, the condition is `Qhi <= E + 2l` for N = 5, 6 (`sh6_cond_iff`).
- For N <= 4 it is `Qhi <= E + l` (Bmg's `ctree1_box_exact`).
- The inner nodes get `lo(inner -> root)` from dist_min. The root gets it from MaxMin.

## Model (named hypotheses, Int ps, every delay a function of the tree position)

- H_PIN_READ (`Sol`): each node obeys `CelEq`: for t >= 0 it is `cSpec` (the real bd_c2/c3/c4 INIT, `NecessityMerge.c*_cspec`) of
  - its pins, where pin j reads child j's output at `rd(j::p).σ t`;
  - its own output, read at `fb(p).σ t`.
- H_RESET: every node is 0 before time 0.
- Box: `rd q` is in [lo q, hi q] with 0 <= lo <= hi, and `fb p` is in [Qlo p, Qhi p] with 1 <= Qlo <= Qhi.
- H_PIN_FIFO: every edge read map is monotone. Different pins are independent. Feedback maps are arbitrary.
- H_LEAF (`LeafOK`): each leaf has one clean edge per phase, at strictly increasing times, the first one at >= 0. Its values go 1, 0, 1, ...
- H_ACK (`HAck`): each leaf's phase-(k+1) edge comes >= E (E >= 1) after the root's ideal phase-k edge.
  - That ideal edge is `Tm`, the zero-delay tree of the pin reads. In a correct run it equals the real root's edge.
- Spec (`Good` / `TreeOK`): at every node, every possible output equals the zero-delay C-element of the node's (ideal) children's reads. This must hold for every map in the box, both read maps and feedback maps.

## Results (all `[bchk] OK`; axioms only propext / Classical.choice / Quot.sound)

| theorem | statement |
|---|---|
| `tree_box_exact` | **headline**: `TreeOK <-> Cond` (H_CTREE_LOOP at every node and every child), for any `Wf` tree (fan-in >= 2). Side conditions: 0 <= lo <= hi, 1 <= Qlo <= Qhi, E >= 1. |
| `tree_suff` | sufficient direction. It holds for every monotone read map in the box. |
| `tree_needs` | necessary direction, with a counter-trace (details below this table). |
| `bridge_phase` / `bridge_hold` / `bridge_needs` | one node of any arity whose inputs are phase traces read through monotone maps. Its ideal output is a phase trace with edge times = max of the arrival times (`rho`). HHold holds if every next arrival is at least `Qhi` after the edge, and fails at phase 0 when an early pin and a late pin straddle the loop. |
| `arrive_bound` | the tree-level causal bound that Bmg was missing: pin j's next arrival is at least `edge + dist_min + E + MaxMin + lo`. |
| `cond_iff` / `CondR` | the condition as a per-node recursion (decidable for concrete trees) |
| `sh6_cond_iff` | N = 6 with uniform delays: the condition is `Qh <= E + 2 l` |
| `sh6_numbers` | Box numbers: read lo 145 (wire 100 + arc 45), read hi 524, loop [95, 424], E = 300. H_CTREE_LOOP holds (424 <= 590), so every run is glitch-free. The old row fails at the inner C4: Spread 79 + 300, plus fmax 300, gives 679 > 445. |
| `sh6_glitch` | the same numbers with the loop at 591: not TreeOK |
| `nonvacuous` | an env meeting every hypothesis exists (sh6: maps at 145, leaves every 2000 ps), and a run exists |
| `old_imply_new` | the old lumped StaticOK form, per node, implies the new one |

The counter-trace of `tree_needs`, for a failure at node n and child c:
- Every map is constant at its lo.
- In phase 0 the leaves below n switch late (at `MaxMin(root)`), so n is the critical input of every ancestor.
- In phase 1 every leaf switches exactly E after the root edge, except the leaves below a sibling of c, which wait longer.
- Then c's next edge reaches n while the sibling still reads phase 0, less than `Qhi` after n's own edge. `cel_box_exact`'s adversarial feedback map then glitches n.

Binary model: the exact condition is `<=`. The JSON's strict `+1` (Bs) stays on top.

## Findings for the cell owner / JSON

1. **Replace `bd_ctree.node_fork` with `bd_ctree.node_loop`** (draft above). It has one form per (node, child) and is launched at the node's O6 edge.
   - The data side is feedback wire hi + feedback site pin hi + feedback arc hi. The feedback pin is I2, I3 or I4 by fan-in. The old row lumped this pin into `fmax`.
   - The request side uses only lo values.
   - Nothing that passed the old row fails the new one.
   - On a route, the new row needs per-pin lo values of the tree's internal and port wires, and the env `E`.
2. The old row's `Spread` (port wires included) is the term that fails on real box numbers (`sh6_numbers`: 379 ps of spread). It is not a real race.
3. For N <= 4 (one node), the old row's port-wire spread also cancels. It reduces to `ctree1_box_exact`, `Qhi <= E + min lo`. That bound is already in Bmg's note.

## NOT covered

- The protocol: H_ACK is assumed (`bd_ctree.ack_wait`).
- The env from the root to the leaves is one lower bound E, the minimum over leaves. A per-leaf E_i would give `min` over the leaves below c in place of E. This is argued, not proved.
- Correlated corners: the box treats every pin independently. For a corner model, apply the theorem per realisation.
- Kleene X windows.
- Fan-in >= 2 is assumed. A 1-wide chunk is a wire, i.e. a leaf, which is how bd_ctree builds it.
- The JSON is not edited (draft only).

## Check

    /tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/bchk.sh formal/lean/Formal/Cells/CTreeExact.lean
    -> [bchk] OK: formal/lean/Formal/Cells/CTreeExact.lean

Axiom audit: `/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Bct/ax.lean`
(14 theorems; at most propext, Classical.choice, Quot.sound). No sorry, admit,
native_decide or axiom.
