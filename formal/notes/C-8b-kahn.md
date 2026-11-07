# C-8b: Kahn determinacy and the gcd loop (track 8, composition: dataflow semantics)

## Verdict

**Works, at the untimed token level.** Core Lean only (no Mathlib), no sorry/axiom/
native_decide; `formal/check.sh` passes on all six files (966 declarations audited).
Proved:
1. a general determinacy theorem for token dataflow graphs (FIFO channels, any
   schedule): every complete firing sequence from a state ends in the same state
   after the same number of firings, and no schedule runs longer;
2. the gcd kernel's main loop, built as a dataflow graph three ways (textbook Kahn
   mux header; Dynamatic-style `control_merge` header; inner strip loop as a real
   nested loop), outputs exactly what the C loop returns, under every schedule,
   for every input on which the C loop terminates, and that is `Nat.gcd` on the
   loop's entry condition;
3. the whole C function (binary gcd, as transcribed) equals `Nat.gcd` for all
   natural inputs.

The gap to the bundled-data circuit is large and is all in track 8a (below).

## What checks (run command)

```
cd formal && ./check.sh Formal/Net/KahnLTS.lean Formal/Net/Kahn.lean Formal/Net/KahnGcd.lean \
  Formal/Net/KahnGcdCM.lean Formal/Net/KahnBounded.lean Formal/Net/KahnGcdNested.lean
```
(about 6.5 min wall through slot.sh; KahnGcdNested and KahnGcd are the slow ones,
mostly the 12x21 / 18x30 `cases` in the producer/consumer tables).
Single file: `cd formal/lean; export LEAN_PATH=$PWD/.lake/build/lib/lean;
../slot.sh lean -o .lake/build/lib/lean/Formal/Net/X.olean Formal/Net/X.lean`, in
dependency order KahnLTS, Kahn, KahnGcd, then the other three.
The lead has to add these six modules to `Formal.lean` (I do not own it).

| file | main theorems |
|---|---|
| `Formal/Net/KahnLTS.lean` | `residual`, `prefix_run`, `terminal_unique`, `no_divergence` (abstract LTS, diamond on an invariant) |
| `Formal/Net/Kahn.lean` | `Node` (Kahn-monotone firing), `WF`, `WFOn`, `wf_diamond`, `wfOn_diamond`, `wf_determinate`, `wf_no_divergence`; node library `strict op1 op2 fork branch sink mux`; `merge_not_determinate`, `merge_not_wf` |
| `Formal/Net/KahnGcd.lean` | `gcdC_eq` (whole C fn = `Nat.gcd`, all inputs), `cLoop_gcd`, `G_wf`, `run_of_cLoop`, `dataflow_eq_cLoop`, `dataflow_gcd` |
| `Formal/Net/KahnGcdCM.lean` | `G2_closed`, `G2_wfOn`, `cm_dataflow_eq_cLoop`, `cm_dataflow_gcd`, `two_invocations_not_inv` |
| `Formal/Net/KahnBounded.lean` | `wfB_diamond`, `wfB_determinate` (capacity-bounded FIFOs), `cap1_dataflow_eq_cLoop` |
| `Formal/Net/KahnGcdNested.lean` | `G3_wf`, `inner_loop` (inner dataflow loop computes `strip2`), `nested_dataflow_eq_cLoop`, `nested_dataflow_gcd` |
| `Wip/C8b/sim_two_invocations.py` | simulation, not proof: two invocations through the `control_merge` graph |

## The model

* Store `C -> List V`: each channel an unbounded FIFO (bounded variant in
  KahnBounded). A firing pops `k c` from the front of input channels and appends
  `p c` to output channels.
* `Node.mono` (Kahn's condition per firing): if a node can fire on `s`, it fires
  identically on any `s'` whose input channels extend `s`'s at the back. Whether
  it fires and what it does depend only on a prefix of its own inputs.
* `WF`: each channel has at most one consumer node and at most one producer node.
* Step: any enabled node fires (free schedule). Determinacy proof: the one-step
  diamond (two distinct enabled nodes commute and do not disable each other),
  then a standard residual argument (`KahnLTS`): a label enabled now is fired by
  every terminating run, so all terminating runs are permutations of each other.
  This is strong confluence plus termination-length uniqueness, stronger than
  needed for "same output": it also gives "if one schedule terminates, all do".
* Values `Nat`; condition tokens `v != 0`.

## The C source, and how the graph matches it

There is no gcd under `kernels/`: gcd is Dynamatic's own integration test. Its
lowering is in `cloud/fixtures/frontend/gcd/comp/` (`cf_transformed.mlir`,
`handshake_transformed.mlir`); `cells/hw/uniform_oracle.py:k_gcd` transcribes it.
It is **binary (Stein) gcd**, not Euclid: early returns for 0, a shared-twos loop
(bb3), strip-twos loops for a and b (bb5, bb7), then the main loop (bb8-bb11)
`diff=a-b; if(a<b) b=a; a=|diff|; strip twos from a` until `a==0`, return `b<<k`.

* `gcdC` transcribes the whole function; `gcdC_eq`: `gcdC a b = some (Nat.gcd a b)`
  for all `a b : Nat`.
* The dataflow graphs implement the main loop only (`cLoop`), the part with a
  loop-carried pair through mux/branch. The prologue loops (bb3/bb5/bb7) are not
  in the graph; they have the same shape as the inner loop of `G3` and would be
  more of the same.
* Graph shape vs Dynamatic's: Dynamatic tests `a==0` at bb8 (entry) and bb9 (back
  edge) and computes `min` with a `select` in bb9; my graphs test at the loop
  header and compute `min` as an operator node. Same function, slightly different
  topology. `G` and `G2` fold the inner strip loop into one operator node;
  `G3` makes it a real nested loop.
* `dataflow_eq_cLoop` needs no hypothesis on the inputs: for every `(a, b)` and
  fuel on which `cLoop` returns `r`, every complete run ends in `fin r`. On the
  loop's entry condition (b odd, a odd or 0, which the C prologue establishes)
  `cLoop` terminates with `Nat.gcd a b` (`cLoop_gcd`). Where the C loop does not
  terminate (e.g. b = 0, a odd: unreachable in the C) nothing is claimed.

## Mux versus merge, and why bdc's choice matters

* `mux` is deterministic: which input it reads is a function of the select token
  already in its FIFO, and it never touches the unselected input. It is a `Node`;
  graphs of muxes, branches, forks, joins and operators are `WF`, hence determinate
  unconditionally. This matches bdc's lowering of `mux` to `bd_mux`, which acks
  only the selected input (bd-config.json).
* `merge` / `control_merge` are nondeterministic: in this framework a merge is two
  labels (one per input) that share the output channel. Each label alone is a fine
  `Node`; only `WF`'s unique-producer clause fails (`merge_not_wf`), and without it
  determinacy really fails (`merge_not_determinate`: outputs `[1,2]` vs `[2,1]`).
  A priority merge (Dynamatic's `merge.v`: first valid wins) is not even a `Node`:
  it violates `mono` (a late token on the higher-priority input changes the choice).
* Dynamatic's loop headers are NOT textbook Kahn: they use `control_merge` on the
  control tokens and drive the data muxes from its index (gcd bb10: `mux12..14` +
  `control_merge9`; bb11 likewise). bdc lowers every >=2-input `control_merge`/
  `merge` to `bd_arbiter + bd_mux`. `KahnGcdCM` shows such a graph is still
  determinate under **H_ONE_INVOCATION**: at most one token on the loop's control
  ring (`start`, `hC`, `backC`). That invariant is closed under every firing
  (`G2_closed`) and makes the two merge labels never co-enabled (`G2_wfOn`), which
  is what `WFOn` needs. So the arbiter in a `control_merge` never decides a real
  race at token level: its outcome is forced, and determinacy does not depend on
  which way it resolves.
* With two invocations in flight (two start tokens; `two_invocations_not_inv`)
  the invariant fails. Simulation (`Wip/C8b/sim_two_invocations.py`, not a proof):
  output ORDER becomes schedule-dependent (`(1,7)` or `(7,1)` for pairs (3,5),(0,7));
  values stay correct over a 420-input sweep, because the a/b/control tokens keep
  their pairing through the same index sequence. The textbook primed-mux graph
  `G` gives `(1,7)` always (it is `WF`). So: a kernel with one call in flight
  (gcd_rig resets between vectors) is determinate either way; a pipelined
  multi-call use of a Dynamatic loop is not, and that is a property of
  `control_merge`, not of bdc's cells.
* Why bdc's "trust the arbiter" is consistent with this: token-level exclusivity
  (what is proved here) does NOT give handshake-level serialisation: the return-to-
  zero of one input's handshake can overlap the next request on the other input.
  bd_merge needs serialisation (AUDIT.md section 1); bd_arbiter does not. Proving
  that the arbiter's handshake implements the `control_merge` token rule under
  token exclusivity is a track-8a obligation.

## Bounded channels

`KahnBounded`: capacity `cap c` per channel, a node fires only if the channels it
pushes into stay within capacity. The diamond still holds for `WF` graphs (firing
one node can only free space in another node's output, by unique producer), so
every schedule reaches the same terminal state, which may now be an artificial
deadlock. `cap1_dataflow_eq_cLoop`: with capacity 1 everywhere the gcd graph `G`
still never deadlocks and gives the C result.

## Gap to the bundled-data circuit (what track 8a must close)

This is the untimed Kahn layer only. Missing, in order:
1. **Channel refinement.** A bundled-data channel is req/ack/data wires. Without a
   storage cell it is a rendezvous (capacity 0: producer and consumer fire together),
   with a `bd_link` it holds one token with a bubble discipline. Neither is exactly
   "FIFO of capacity k". Need: a four-phase handshake trace over a channel (with or
   without links) corresponds to a token sequence, and a ring needs enough storage to
   not deadlock (track 9's "three stages per cycle"); my capacity model would have to
   encode rendezvous channels as joint firings.
2. **Cell refinement.** Each cell's req/ack behaviour must implement its node's
   firing rule: bd_fork (ack via bd_ctree), bd_steer (cond_br), bd_mux (ack only the
   selected input), bd_join, bd_src/bd_snk, compute wrappers, and
   `bd_arbiter + bd_mux` for control_merge under H_ONE_INVOCATION.
3. **Bundling.** Data valid at the consumer when req arrives (the bundling
   constraint, track 6); here a token's value is simply there.
4. **Datapath.** Operators are Lean functions on `Nat`; the circuit computes int32.
   H_NONNEG31 (not proved): for inputs in [0, 2^31) (the oracle's 31-bit masks) every
   intermediate value lies in [0, max a b], so subtraction/abs/compare/shift never
   wrap and signed ops agree with `Nat` ones. Testable by an exhaustive-width BitVec
   model or the existing `bdc/test_compute.py` gate.
5. **Timing / arbitration physics.** No delays, no metastability. The arbiter is a
   decision whose outcome is irrelevant only because exclusivity holds; its
   resolution time is the track-7 analog question.
Once 1-3 give a simulation relation "every circuit trace projects to a run of the
token semantics", determinacy and `dataflow_gcd` transfer to the circuit for free;
that is the payoff of doing this layer first.

## Fidelity of the primitives used

| primitive | model | fidelity |
|---|---|---|
| channel | unbounded (or capacity-k) FIFO of values | abstraction of req/ack/data; exact for Kahn semantics, not for handshake timing or rendezvous channels |
| mux, branch, fork, op, sink, constant | Kahn-monotone firing rules | match Dynamatic's handshake op semantics (HandshakeOps.td) at token level; not checked against the bd_* cells' RTL |
| control_merge | two merge labels sharing outputs | Dynamatic's documented semantics (nondeterministic merge + index); bd_arbiter's choice is the free label choice |
| values | `Nat` | int32 only under H_NONNEG31 (not proved) |
| C kernel | `gcdC`, `cLoop` hand transcriptions of cf_transformed.mlir | hand transcription, cross-checkable against uniform_oracle.py:k_gcd; not machine-extracted |

## Effort to finish / extend

* Whole gcd handshake graph (all 13 blocks, ~150 ops) imported mechanically from
  `handshake_transformed.mlir` (bdc/hs parser emitting Lean `Node` terms), with
  `control_merge` everywhere and `WFOn` + a one-token invariant: ~1 week. The
  schedule proofs are mechanical (rfl / simp, as here); the producer/consumer
  `cases` tables scale as nodes x channels and need a decision procedure rather than
  `simp_all` per case beyond a few hundred nodes.
* Track 8a's refinement (handshake -> token) is the real work: weeks, and it is
  where the project-specific risk is.

## What it buys the project

* A proof that the dataflow layer bdc consumes is determinate exactly when there is
  at most one token per `control_merge` ring, and that bdc's per-op choices (mux to
  bd_mux acking only the selected input; never bd_merge) preserve the semantics this
  proof needs. A future op lowering can be checked against `Node.mono` + `WF`.
* A reference semantics against which board/GLS traces can be compared: any complete
  run must end in `fin (gcd a b)`, whatever the arbitration and timing.
* The determinacy theorem is generic, so per-kernel results (collatz, ipow, isprime)
  reduce to exhibiting ONE schedule, as done here.

## Decisions taken (no one to ask)
* gcd is binary gcd, so "Euclid by subtraction" was matched to the C's main loop,
  which is subtraction-based Euclid with twos stripped; correctness goes through
  `Nat.gcd` lemmas in core (`gcd_sub_self_left`, `Coprime.gcd_mul_left_cancel`).
* Determinacy via the diamond property rather than Kahn's fixpoint (CPO of
  streams) semantics: it needs no domain theory, works in core Lean, and gives the
  stronger "same terminal state, same length" result. Kahn's continuity for
  infinite streams (non-terminating runs) is not covered; `no_divergence` covers
  the terminating case, which is the one a kernel cares about.
