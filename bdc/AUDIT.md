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

## 3. `handshake.select` is arithmetic, not a mux

**Status: confirmed. `COMPILER-PLAN.md`'s Stage 2 table grouped `select` with
`mux` and `control_merge` under `bd_mux`. That is wrong and would leak a
token on every firing.**

`SelectOp` is not in `HandshakeOps.td` with the channel operations at all. It
is defined in `include/dynamatic/Dialect/Handshake/HandshakeArithOps.td:570`,
as a `Handshake_Arith_Op`, in among `addi`, `ori` and `cmpi`:

> `let summary = "Select a value based on a 1-bit predicate.";`
> `let arguments = (ins ChannelType:$condition, ChannelType:$trueValue,`
> `                     ChannelType:$falseValue);`

All three operands are ordinary consumed inputs — an arith op joins its
operands and produces its result. That is the exact opposite of what
`bd_mux` does, and `bd_mux`'s own header is explicit about it:

> "Only the selected input is acknowledged... The other input keeps its
> token, untouched, **which is exactly what a loop header needs**."

Keeping the unselected token is the *feature* that makes `bd_mux` right for
`mux` and wrong for `select`. Lowering `select` to `bd_mux` would strand a
token on the unchosen input at every firing; against the standing
one-token-per-loop invariant that is a hang, and it would be silent.

**Consequence:** `select` is a Stage 3 compute unit — a 2:1 datapath
multiplexer, one LUT3 per bit, inside the compute wrapper with all three
inputs joined. 3 occurrences in the four kernels. Recorded in
`bdc/bd-config.json`.

---

## 4. Zero-width control channels, and what they cost

**Status: measured.**

A handshake control channel is `<>` — req and ack, no data. Every
data-touching cell in `cells/rtl/` declares `[W-1:0]`, and `W=0` is illegal
Verilog, so a control channel cannot be spelled `W=0` without changing a
frozen library.

It does not need to be. Measured with `yosys synth_xilinx` on `bd_mux`:

| instantiation | LUTs |
|---|---|
| `W=8`, data read | 4×LUT1 + 1×LUT2 + 4×LUT6 + 4×LUT6_2 |
| `W=1`, data read | 4×LUT1 + 1×LUT2 + 1×LUT3 + 4×LUT6 |
| `W=1`, data output **dangling** | 4×LUT1 + 1×LUT2 + 4×LUT6 |

The datapath LUT disappears when nothing reads the output. So the convention
is **`W=1`, data inputs tied to 0, data output left genuinely unread**, and a
control channel costs exactly zero extra LUTs.

The obligation this puts on the emitter: the data output must stay unread.
Wiring it to a top-level port would put the `LUT3` back, and `lutcost.py`
would then be measuring a cost that the design does not actually need.

Note this never applies to `bd_fork`, `bd_join`, `bd_steer`, `bd_arbiter` or
`bd_ctree` — those have no data ports at all.

---

## 5. What does transfer cleanly

- **`--handshake-materialize` gives one producer and one consumer per value.**
  Its description: "Ensures that every SSA value within Handshake functions is
  used exactly once by inserting forks and sinks as needed." This is a
  structural property of the graph, with no timing content, so it transfers
  intact — and it is exactly the channel discipline `COMPILER-PLAN.md` wanted.
- **`fork`, `join`, `cond_br`, `source`, `sink`, `constant`** are structural.
  Their bundled-data equivalents carry their own timing obligations, discharged
  inside `cells/rtl/` and already gated by `cells/check.sh`.
- **Bitwidths** from `--handshake-optimize-bitwidths` are pure dataflow facts.

---

## 6. Containing a C-element is not the same as providing storage

**Status: confirmed, while building `bdc/slack.py` (COMPILER-PLAN Stage 4/5's
cycle-storage checker). Not a correction to anything already written down —
the brief for that module posed this as an open question and asked for the
evidence either way.**

`slack.py` has to decide which handshake ops "provide storage" for the
purpose of COMPILER-PLAN's cycle rule: every cycle in the dataflow graph
needs at least one node that can hold a token independent of what its
neighbours are doing, or the cycle is a combinational loop no routing fixes.
The obvious candidate is `buffer` (`bd_link`/`bd_pipe`), but `rtl/bd_ctl.v`
and `rtl/bd_ce.v` put C-elements (Muller gates — real bistable circuits, with
a `rst` pin and a `(* keep *)` feedback loop identical in shape to the one
inside `bd_link`) into `bd_fork`, `bd_join` (via `bd_ctree`), `bd_mux`, and
`bd_arbiter` as well. The question worth asking by name: does having a
C-element make a cell "storage" too?

### The answer is no, and `bd_ctree`'s own header already says why

> "Under the discipline this cell is actually used with... every input is a
> request that rises once and falls once per transaction, all of them rise
> before any falls, and nothing moves again until the acknowledge has
> completed the cycle. Every sub-tree therefore returns to zero every cycle
> and can never be stale."

A C-element used this way is a **rendezvous** primitive, not a **token**
primitive: its bistability exists to give a hazard-free decision for the ONE
transaction currently in flight, and it is required to have fully reset by
the time the next transaction starts. There is no state left over for a
second, concurrent transaction to rest on — which is exactly the property a
cycle needs from a storage node, so it can hold a token at rest on one side
while the rest of the loop is still catching up.

`bd_mux`'s join C-elements (`j0`/`j1` in `rtl/bd_mux.v`) are built the same
way and reduce to the same argument. `bd_mux`'s datapath (`bd_datamux`,
`rtl/bd_latch.v`) is stated outright to be plain combinational muxing — no
latch at all.

`bd_steer` (`rtl/bd_ctl.v`) makes the point from the other direction: it
routes a handshake with **no C-element and no reset at all** ("No feedback
wire, so no keep attribute, no loop for nextpnr to be told about, and no
reset"), and nobody would call it storage. If a cell with a rendezvous
C-element and a cell with none are both non-storage, the C-element's mere
presence was never the deciding property.

### The one case that looked different, and still isn't

`bd_arbiter`'s state node (`bd_c2n_set` inside `bd_arbcell`, `rtl/bd_arb.v`)
is NOT reset every transaction — it deliberately remembers who won last,
across arbitrarily many transactions, so contention alternates fairly. That
is genuinely longer-lived state than `bd_ctree`'s, and it was worth checking
carefully for that reason. But what it remembers is a **priority bit**, not
a **data token**: it does not let one side of a data cycle sit at rest,
value intact, while the other side of the loop advances — which is the
actual property `slack.py`'s check needs. An arbiter in a cycle changes
nothing about whether that cycle can be phased with zero storage elsewhere
in it.

### What does count, and the one place this cuts the other way

`bd_link`/`bd_pipe` (`rtl/bd_link.v`) count because their `bd_latch`
(`rtl/bd_latch.v`) is different in kind, not just in degree: it is
level-sensitive storage, opened and closed by the local handshake rather
than reset every transaction, and its own file header opens with "Storage
without a clock edge." `bd-config.json` already maps exactly one op onto
these cells (`buffer`), and this audit entry confirms that mapping is the
whole set — nothing else in `cells/rtl/` needed adding to it.

The one cell that came close to arguing the other way is `bd_mem`
(`rtl/bd_mem.v`): it instantiates a real clocked `RAMB18E1`, a genuinely
stronger storage element than a latch. `load`/`store`/`mem_controller` are
NOT counted as storage by `slack.py` regardless, and the reason is not the
RTL — it is that `bd-config.json` marks all three `"kind": "todo"` with no
committed `cells` entry (Stage 6 is unbuilt), and section 2 above already
says none of Dynamatic's cycle-level memory guarantees are safe to assume
without their own audit entry. Crediting an unbuilt, unaudited op with a
correctness-relevant property here would be exactly that mistake. Concrete
consequence, measured against the four kernels in `build/frontend/`: every
kernel that touches memory (`single_loop`, `fir`, `gcd`) has at least one
cycle that closes purely through a `mem_controller`'s own address echo
(`mem_controller -> load -> mem_controller`, with no `buffer` anywhere), and
`slack.py` reports it as a hard error today. That is an open question for
whoever builds Stage 6, not a bug in the checker — once `mem_controller`'s
real cell mapping is committed to `bd-config.json`, `bd_mem`'s `RAMB18E1`
will very likely need adding to the storage set, and this entry is the
pointer to why.

---

## 7. The memory station, and what a working prototype does not discharge

**Status: prototype built, simulated and routed. `bd-config.json` deliberately
unchanged — this entry is the evidence, not the mapping.**

`bdc/mem.py` generates the two modules a memory access needs, and they are real:
they simulate against a bench with its own oracle, and they place, route and
resize through the default `cells/flow.sh` path. None of that, on its own,
licenses `load`/`store`/`mem_controller` in `bd-config.json`. What it does is
turn section 2's "memory is the last thing to attempt" into a specific list of
what is now known and what is still open.

### The shape: a memory access is a compute unit whose function is the RAM

`bdc/compute.py` emits a unit as *join the operands, wait a matched delay, raise
the outgoing request*. A memory station is the same unit with the RAM standing
where the `bd_delay` stands. `bd_mem`'s `DSETUP` (address and data settled
before the manufactured clock rises, rule B) and `DCO` (acknowledge trails the
read data out of the RAM, rule C) **are** that matched delay, and
`verify/tighten.py` already audits both. The station therefore contains no
`bd_delay` of its own, and no `uor` — which is deliberate, because that is how
rule A recognises a request boundary it should be sizing, and this cell does not
have one.

Split into a **port** (owns the RAMs) and **stations** (one per access) because
the port is untestable otherwise: a `RAMB18E1` cannot be given an `INIT` here,
so the only way to read a known value is to store it first, which needs two
stations on one port.

### Three things the RTL had to get right, and the negative controls for each

**The operands are released when the PORT is quiet, not when the consumer is
done.** My first version used `bd_join`, on the belief that its acknowledge
already gave four-phase ordering. Reading `rtl/bd_ctl.v` falsified that:
`bd_join` is `bd_ctree` over the input requests plus `assign ack_out =
{N{ack}}`, so the outgoing request depends on the inputs only and there is *no
arc from the acknowledge at all*. With the address released at `z_ack`, the next
access arrives while the manufactured clock is still high and there is simply no
second rising edge for it — a silently swallowed access, not a hang. The fix is
an asymmetric C-element, `q = ~rst & (a | (q & b))` with `a = z_ack` and
`b = p_ack`: it rises on `z_ack` alone so the producer learns promptly, and
falls only when the port has returned to zero. `INIT 64'h00EA` is `bd_c2`'s
`0x00E8` with exactly one bit changed — the code where `a` alone is high. That
bit is the asymmetry and it is the whole cell. The bench keeps the broken
version reachable as `BDC_MEM_NAIVE_ACK=1`.

**`p_ack` is shared, so the outgoing request must be gated by this station's own
claim** (`z_req = p_ack & joined`). Ungated, the *other* slot's acknowledge
looks like a second result on this channel.

**The bench counts RAM clock edges.** `always @(posedge ram_clk) nedges =
nedges + 1`, checked against the access count at the end. 60 accesses, 60 edges.
This is the check that would have caught the swallowed access on its own, and it
is the reason the station is testable at all.

Negative control for the sizing: the same design with `DSETUP = 0` reports 106
and 107 setup violations where the sized port reports 0 and 0.

### What routing added

`flow.sh` closes on it: 2 `RAMB18E1`, 417 LUT cells, no global clock buffer.
`verify/resize.sh` settles in 4 sweeps / 17 place-and-route runs on
`UMEM0_UCO 9, UMEM0_USETUP 1, UMEM1_UCO 9, UMEM1_USETUP 8`, with rule B margins
of 402 and 2759 ps and rule C margins of 981 and 1353 ps.

Two constraints that fall out of the hardware rather than the design:

- **The port is 16 bits.** `RAMB18E1` in x18 mode has 16-bit `DIADI`/`DOADO`.
  Anything wider is a **gang** of RAMs with their acknowledges joined by a
  `bd_ctree` — which is what `emit_port` builds — not a wider RAM.
- **`AW > 10` truncates.** The address is `{addr, 4'b0000}` taken from the TOP of
  `ADDRARDADDR`, so an eleventh address bit folds the memory in half without
  saying anything. `check()` refuses it loudly.

And one that is worth stating because nothing else audits it: **`DCO` is also the
address HOLD guard.** The address is released one arc after `p_ack` falls, and
`p_ack` falls `DCO` after `ram_clk` falls. Shortening `DCO` shortens hold. Rule C
sizes it for clock-to-out and would not notice.

### What this does NOT discharge

`mem_controller` is where the program order lives, and it is unbuilt. A
four-phase trace for a program-order token chain works on paper, with **one
ordering assumption that could not be discharged by construction**: releasing
the token when `p_ack` falls races the previous station's `z_ack` fall, and it is
currently safe only because the port path is roughly 20 arcs against the
consumer path's 2. A margin that large is not an argument, it is a coincidence
with good odds — it needs either a real interlock or a rule that measures it.

Until then section 6 stands unchanged: `slack.py` still reports a cycle closing
through a `mem_controller` address echo as a violation, and `bd-config.json`
still marks all three ops `"kind": "todo"`. When the mapping is committed,
`bd_mem` will need adding to `STORAGE_CELLS`, and this entry plus section 6 are
the pointer to why.

Sharing one port between accesses is `bd_arbiter`'s job — the library's own
recommended answer, and section 1 already argues for arbitrating
unconditionally rather than building analyses to avoid it.
