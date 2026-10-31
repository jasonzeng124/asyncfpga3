# C-9b: verified ring-depth checker (track 9 companion)

## Verdict

**Works.** A core-Lean checker for "every cycle carries >= k storage stages",
proved sound and complete against both closed walks and simple cycles, with
no hypotheses (it is a pure graph statement). Run on the graphs bdc's own
`ring_depths()` sees for all 9 frontend fixtures: it agrees with emit.py on
every one. All 9 fixture graphs are *proved* (kernel `decide +kernel` on a chunked
certificate; no native_decide) to satisfy the 3-stage floor on ring_depths'
own output, gcd included (883 s).

## Files

- `formal/lean/Formal/Net/RingCheck.lean` -- graph, `Walk`, `AllCyclesGe`,
  the executable checker `check` (per-source capped Bellman-Ford to a
  fixpoint), `check_iff`.
- `formal/lean/Formal/Net/RingCheckSimple.lean` -- explicit edge-list cycles,
  `IsSimple`, `AllSimpleCyclesGe`, `allCyclesGe_iff_simple`,
  `check_iff_simple`.
- `formal/lean/Formal/Net/RingCheckCert.lean` -- certificate checker for the
  kernel: `certCheck_sound`, `certCheck_complete`, `allCyclesGe_iff_cert`.
- `formal/tools/ringcheck/export.py` -- runs bdc (emit.Emitter) on handshake
  MLIR, exports the graphs to Lean, an untrusted Python reference, and
  per-kernel certificate files.
- `formal/lean/Wip/C9b/BdcGraphs.lean` (generated) -- all graphs + `#eval`s.
- `formal/lean/Wip/C9b/certs/Cert_<kernel>_<func>.lean` (generated) -- one
  kernel-checked theorem `<kernel>_<func>_rd_ge3 : AllCyclesGe g 3` each.
- `formal/lean/Wip/C9b/python_ref.json` (generated) -- Python's answers.

The generated files are under Wip/ only because they are generated data the
lead may or may not want in the claimed tree; they contain no sorry/axiom/
native_decide and the cert theorems are genuine proofs. Promote by moving
them to `Formal/Net/` (the lead's call: they take build time, gcd most).

## Theorems proved (all: axioms = propext, Classical.choice, Quot.sound)

- `Formal.Net.RingCheck.check_iff : check g k = true ↔ AllCyclesGe g k`
  where `AllCyclesGe g k := ∀ s c, Walk g s s c → k ≤ c` (every closed walk
  of >= 1 edge has weight >= k).
- `allCyclesGe_iff_simple : AllCyclesGe g k ↔ AllSimpleCyclesGe g k` (closed
  walks vs simple cycles, Nat weights: the segment between the first repeated
  source is a lighter-or-equal simple cycle).
- `check_iff_simple : check g k = true ↔ AllSimpleCyclesGe g k` -- the
  checker decides CLAUDE.md's rule ("three storage stages per simple cycle")
  exactly.
- `certCheck_sound`, `certCheck_complete`, `allCyclesGe_iff_cert`.
- Supporting: `iter_spec` (fuel `numNodes*k+1` always reaches a fixpoint,
  via the strictly decreasing table sum), `inv_step` (every value < k is
  witnessed by a walk), `fix_complete` (a fixpoint lower-bounds every walk).
- Generated: `<kernel>_<func>_rd_ge3 : AllCyclesGe <graph> 3` for every
  fixture whose kernel check finished (table below).

Graph model: list of edges `src -> dst` with Nat weight (storage stages on
that channel); parallel edges and self loops allowed; node weights would be
folded into out-edges by the exporter (bdc has none: only links store).

## How to run

    cd formal/lean && export PATH=$HOME/.elan/bin:$PATH
    export LEAN_PATH=$PWD/.lake/build/lib/lean
    ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/RingCheck.olean Formal/Net/RingCheck.lean
    ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/RingCheckSimple.olean Formal/Net/RingCheckSimple.lean
    ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/RingCheckCert.olean Formal/Net/RingCheckCert.lean
    cd ../.. && python3 formal/tools/ringcheck/export.py --cert-dir formal/lean/Wip/C9b/certs \
        formal/lean/Wip/C9b/BdcGraphs.lean cloud/fixtures/frontend/*/comp/handshake_transformed.mlir \
        > formal/lean/Wip/C9b/python_ref.json
    cd formal/lean && ../slot.sh lean Wip/C9b/BdcGraphs.lean          # #eval evidence, ~17 s
    ../slot.sh lean Wip/C9b/certs/Cert_collatz_collatz.lean           # proof, ~9 s

## What was exported (exactly ring_depths()'s graph)

Nodes = `func.nodes` indices; edges = `slack.build_node_graph(func)` minus
`em.mem_absorbed` (as ring_depths does); weights, three variants:
- `rd`: `ring_depths(func, em.linked, exclude=em.mem_absorbed)` -- the table
  whose postcondition is "lightest cycle >= RING_MIN_STAGES".
- `final`: `em.depth` -- what is emitted (ring_depths, then
  `_apply_ring_pad`, `_apply_slack_stages`, `_apply_link_depths`, which only
  raise depths). NB `em.depth` is NOT ring_depths' output; the exporter
  calls ring_depths again to get it.
- `pre`: 1 per linked channel (before ring_depths deepened anything): a
  negative control that must fail.
- `rs`: what `bdc/ring_stages.py` weighs (per (u,v) max, mem edges kept).

## Results (frontend fixtures in cloud/fixtures/frontend, bdc at this commit)

`#eval` = evidence (compiled evaluation, not a proof). "cert" = kernel proof.

| kernel | nodes/edges | rd: check 3 / min | final: check / min | pre: check / min | rs min | Python FW min (rd/final/pre/rs) | cert proof |
|---|---|---|---|---|---|---|---|
| collatz | 45/66 | true / 3 | true / 3 | false / 1 | 3 | 3/3/1/3 | proved, 6 s |
| collatz64 | 47/67 | true / 3 | true / 3 | false / 1 | 3 | 3/3/1/3 | proved, 7 s |
| fir | 40/52 (+4 mem) | true / 3 | true / 3 | false / 1 | **0** | 3/3/1/0 | proved, 4 s |
| gcd | 239/351 | true / 3 | true / 3 | false / 1 | 3 | 3/3/1/3 | proved, 883 s |
| ipow | 51/73 | true / 3 | true / 3 | false / 1 | 3 | 3/3/1/3 | proved, 17 s |
| isprime | 149/225 | true / 3 | true / 3 | false / 1 | 3 | 3/3/1/3 | proved, 289 s |
| single_loop | 35/45 (+6 mem) | true / 3 | true / 3 | false / 1 | **0** | 3/3/1/0 | proved, 11 s |
| test_loop_free | 39/48 | true / acyclic | true / acyclic | true / acyclic | acyclic | none | proved, 6 s |
| xorshift | 50/71 | true / 3 | true / 3 | false / 1 | 3 | 3/3/1/3 | proved, 13 s |

(min reported as `minCycleCap 1000`; 1000 = acyclic.)

emit.py's own answer: ring_depths() returned without raising for every
fixture, i.e. it claims every cycle >= 3 on `rd`. The verified checker agrees
on all 9; Python Floyd-Warshall agrees with Lean's `minCycleCap` on all 36
graphs. Every cyclic kernel's `pre` graph has a 1-stage cycle (checker says
false), so ring_depths' deepening was necessary everywhere it fired, and the
lightest cycle after it is exactly 3 (it adds no more than needed on the
lightest ring).

## Disagreements found

1. **None between the verified checker and emit.py's ring_depths().**
2. Minor, `bdc/ring_stages.py` (report-only script, not a gate): it does not
   drop `mem_absorbed` edges, so the load <-> mem_controller round trip
   (fir: load0/mem_controller2, load1/mem_controller3; single_loop: two
   more) appears as a 0-stage cycle in its view. ring_stages only reports
   the HEAVIEST ring, so its numbers are unaffected, but it prints spurious
   SCCs like `fir SCC 2 nodes heaviest ring = 0 stages over 0 nodes`
   ("0 nodes" because `best` starts at (0,0) and `tot > best[0]` is never
   true for a 0-weight ring). These are not wire loops (emit absorbs them
   into one station, no net). Removing the mem edges, ring_stages' view has
   lightest cycle 3 everywhere, and its max-collapse of parallel edges
   changes nothing (no parallel edges with differing weights in any fixture).

## What does not work / limits

- `decide +kernel` directly on `check` (the Array-based Bellman-Ford) was
  killed (OOM, 2 min) on collatz's 45-node graph: the kernel is lazy and
  re-evaluates the shared table. Hence the certificate path; certificate
  completeness is proved, so this loses nothing in principle. Kernel cost is
  O(n·|E|·n) list lookups. One `decide` over the whole isprime certificate
  was also OOM-killed, and its 149x149 list literal hit maxRecDepth, so the
  generator emits one def per table row and one `decide` per 8 sources,
  glued by `certCheckFrom_append` (`certCheckFrom_sound` closes it).
- Negative control: the honest capped-distance certificate for single_loop's
  `pre` graph (before ring_depths) is rejected by the kernel
  ("decide proved that ... = true is false"), as it must be.
- `formal/check.sh Formal/Net/RingCheck.lean Formal/Net/RingCheckSimple.lean
  Formal/Net/RingCheckCert.lean` -> `[check] OK` (118 declarations audited).
- The proof is about the exported graph. That the graph is the circuit's
  real handshake topology (fidelity of `slack.build_node_graph` + the
  `mem_absorbed` exclusion + "only links store, a mux/steer/fork/join holds
  nothing") is NOT proved here; it is emit.py's modelling claim
  (H_ONLY_LINKS_STORE, testable by cells/tb/tb_ring.v-style sweeps where a
  mux/steer is inserted into a ring and the minimum live stage count is
  measured; emit.py's comment says this was measured: 1-2 dead, 3 live).
- That 3 is the right floor is track 9a's job, not this probe's.
- The fidelity table of PROGRAM.md (LUTs, routing, FFs) does not apply: no
  gate primitive is modelled here; this is a graph-level verified tool.

## Effort to finish / what it buys

- Done: checker + proofs (~550 lines Lean, core only), exporter, certs.
- To make it a gate (~0.5 day): have bdc (or a CI step) run export.py on each
  emitted kernel and kernel-check the cert; or call the `#eval` checker as a
  second opinion next to ring_depths(). It removes the trust in emit.py's
  hand-written Dijkstra (which, e.g., silently relies on non-negative
  weights and on `cycle_sites` having linked every cycle).
- Extension (~0.5 day): a verified *negative* certificate (explicit cycle
  list, checked via `walk_of_chain`) for kernels that fail, to point at the
  offending ring.
