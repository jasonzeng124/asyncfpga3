# Auditing what transfers from Dynamatic

`bdc/` consumes Dynamatic's `handshake`-dialect output and emits bundled-data
Verilog from `cells/rtl/`. That reuse is only sound where Dynamatic's guarantees
survive the move from synchronous elastic (valid/ready, clocked) to four-phase
bundled data (req/ack, no clock).

This file records the guarantees that were checked, one entry each, with the
evidence. An op mapping that is not written down here has not been audited and
must not be assumed safe.

---

## 1. `handshake.merge` does **not** lower to `bd_merge`

**Status: confirmed. `COMPILER-PLAN.md`'s Stage 2 table has this backwards and
must be corrected.**

### What Dynamatic guarantees

Nothing. `MergeOp` in `include/dynamatic/Dialect/Handshake/HandshakeOps.td:481`
documents itself as:

> "The merge operation represents a **(nondeterministic)** merge operation. **Any
> input is propagated** to the single output."

`ControlMergeOp` (same file, line 607) is likewise "a (nondeterministic) control
merge". Grepping `include/` and `lib/` for any exclusivity annotation or
attribute finds none — the information does not exist anywhere in the IR, so it
cannot be read out. It has to be derived.

Their own implementation confirms the reading: `data/verilog/handshake/merge.v`
loops over the input `valid` bits and takes the first one set. That is a
priority resolver, and it is safe in their world only because a clock edge
samples the decision. There is no clock here.

### What `bd_merge` requires

More than exclusivity. From the cell's own header in `cells/rtl/bd_merge.v`:

> "The obligation, rarely met: exclusivity is not enough. The cell also requires
> that the second input **cannot assert until the first transaction has fully
> completed**, otherwise `C(y_req, z_ack)` fires into a still-high `z_ack` and
> acknowledges a token the merge never carried. **Pipelined code does not
> satisfy that**, which is why the join at the bottom of an if is `bd_mux` and
> not this cell."

So `bd_merge` needs *serialisation*, not just mutual exclusion. Dynamatic exists
to produce pipelined dataflow. The two requirements are in direct opposition.

### Consequence

`bd_merge` is close to dead weight for compiled output. It stays in the library
for hand-written designs, but the compiler should emit it only where an analysis
proves both exclusivity **and** serialisation — and should default to not
emitting it at all.

### What to emit instead

`cells/rtl/bd_mux.v` is the right cell, and its header already says why:

> "Only the selected input is acknowledged... The other input keeps its token,
> untouched, **which is exactly what a loop header needs**."

and, on the difference from the merge:

> "The merge infers which input is live from a request wire, which falls a phase
> too early. The mux infers nothing. `s` is ordinary channel data... That is the
> real argument for paying for a control channel: it converts a timing
> obligation into a data one."

That maps cleanly onto how Dynamatic already structures its output. `MuxOp`
(line 528) is documented as "a **(deterministic)** merge operation" whose

> "'select' operand is received from **ControlMerge of the same block**"

So Dynamatic already emits the pair — `control_merge` decides which predecessor
fired, `mux` selects on that decision:

| op | lowering | note |
|---|---|---|
| `handshake.mux` | `bd_mux` | select arrives as data; direct, no arbiter |
| `handshake.control_merge` | decide + `bd_mux` | see below — the decision is the problem |
| `handshake.merge` | decide + `bd_mux` | never `bd_merge` by default |

### The decision: arbitrate unconditionally, and stop optimising it

`control_merge` derives its index *from which input arrived*, so it cannot be
selected by its own output. Something has to resolve possibly-coincident
requests, and on a LUT fabric that something is `bd_arbiter`.

There is an analysis that would let us skip the arbiter where the graph
guarantees at most one predecessor edge can carry a token at a time — the
standing one-token-per-loop invariant would serialise those inputs by
construction. **We are not doing it.** The arbiter is trusted, on the owner's
call, and the exposure measured in `cells/verify/MTBF.md` is taken as
sufficient.

So the lowering is unconditional:

    handshake.merge, handshake.control_merge  ->  bd_arbiter + bd_mux

This is not merely the conservative choice, it is the *simpler* one. The
alternative made the emitter's output depend on whether a proof succeeded,
which means two lowerings to test, a silent-downgrade failure mode when the
proof is wrong, and a mapping table that cannot be read without also reading
the analysis. Uniform lowering has none of that.

Consequence for sequencing: the token-count analysis is **not** a prerequisite
for the mapping table, and Phase 4 stays where it was. The cycle-storage check
is still required — a cycle with no storage stage is a combinational loop and
no arbitration policy saves it — but that is a separate obligation from this
one.

---

## 2. Cycle-level guarantees do not transfer

**Status: identified, not yet fully enumerated.**

Some of Dynamatic's correctness arguments are stated in clock cycles and
discharged by buffer placement — a pass we deliberately do not run. The
materialize pass documents one directly
(`include/dynamatic/Transforms/Passes.td:171`): it inserts lazy forks on the
control memory network

> "to ensure (together with buffer placement) that multiple group allocations to
> the same LSQ **never happen on the same cycle**."

With no clock and no buffer placement, that guarantee is void. Memory is
therefore the last thing to attempt, and every `mem_controller`/`lsq` guarantee
needs its own entry here before use.

---

## 3. What does transfer cleanly

- **`--handshake-materialize` gives one producer and one consumer per value.**
  Its description: "Ensures that every SSA value within Handshake functions is
  used exactly once by inserting forks and sinks as needed." This is a
  structural property of the graph, with no timing content, so it transfers
  intact — and it is exactly the channel discipline `COMPILER-PLAN.md` wanted.
- **`fork`, `join`, `cond_br`, `source`, `sink`, `constant`** are structural.
  Their bundled-data equivalents carry their own timing obligations, discharged
  inside `cells/rtl/` and already gated by `cells/check.sh`.
- **Bitwidths** from `--handshake-optimize-bitwidths` are pure dataflow facts.
