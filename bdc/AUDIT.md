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

And one that used to be worth stating because nothing audited it: **`DCO` is
also the address HOLD guard.** The address is released one arc after `p_ack`
falls, and `p_ack` falls `DCO` after `ram_clk` falls. Shortening `DCO` shortens
hold, and rule C sizes it for clock-to-out alone.

That is now measured rather than argued. prjxray's `BRAM_L.sdf` has the hold
arcs alongside the setup ones it was already being read for --
`(HOLD ADDRAU (posedge CLKARDCLKU) (-0.566::0.360))` -- so `sim/bd_prims_sim.v`
exports them and `tb/tb_bdc_mem.v` checks them:

    payload held after the edge: addr 2632 ps (need 360), data 2756 ps (need 667)

7.3x on the address and 4.1x on the write data. `DCO` appears twice in that
path -- once inside the clock high pulse, since the request cannot fall until
`p_ack` has risen, and once again on the release -- which is why the margin is
so large, and why rule C's minimum carries hold for free rather than by luck.

Negative controls, because a check that cannot go red is not a check: raising
the requirement to 4000 ps turns it red at the right instant. The interesting
one is the mechanism control, `BDC_MEM_NAIVE_ACK=1`: it does **not** reach this
gate, because releasing operands on `z_ack` trips the return-to-zero monitor
several accesses earlier. Hold is downstream of a hazard that fires first,
which is worth knowing -- it means this gate protects against a future change
to `DCO`, not against the bug the station was built to avoid.

### What this does NOT discharge

`mem_controller` is where the program order lives, and it is unbuilt. The
four-phase trace for a program-order token chain had **one ordering assumption
that could not be discharged by construction**: whether the token may be
released when `p_ack` falls, or must wait for the previous station's `a_ack`.
The argument for `p_ack` was a margin — the port path is roughly 20 arcs
against the consumer path's 2.

`tb/tb_bdc_memseq.v` settles it, and the answer is that the margin was not the
point. Releasing on `p_ack` is wrong **structurally**, at every consumer speed:

| consumer RTZ | release on `a_ack` | release on `p_ack` |
|---|---|---|
| 0 ps | PASS | FAIL, 12 overlaps |
| 1 hop | PASS | FAIL, 12 overlaps |
| 2 hops | PASS | FAIL, 12 overlaps |
| 4 hops | PASS | FAIL, 12 overlaps |
| 8 hops | PASS | FAIL, 12 overlaps |
| 32 hops | PASS | FAIL, 12 overlaps |

Identical counts at every point is the tell that nothing is racing. The RTL
says why. `z_req = p_ack & joined`, so `z_req` falls *because* `p_ack` fell;
the consumer only then drops `z_ack`; and `hold` — hence `a_ack` — needs
`z_ack` and `p_ack` both low. So `a_ack` falls strictly after `p_ack` on every
path, including with a zero-delay consumer. `p_ack` is not an early release
point, it is never a release point.

The consequence for a token chain is a four-phase violation on the a channel,
not a data corruption: the producer offers its next operand into an
acknowledge that never fell. The bench reports both, and it is worth noting
that it reports the data error too — so this one would not have hidden. It
easily could have: the gate here is the a-channel monitor, deliberately not
the data.

`tb/tb_bdc_mem.v`'s sequencer already waits for `a_ack` to fall, so the
prototype was never wrong; the open question was whether it had to. It does.

Until then section 6 stands unchanged: `slack.py` still reports a cycle closing
through a `mem_controller` address echo as a violation, and `bd-config.json`
still marks all three ops `"kind": "todo"`.

**Correction, 2026-08-24: this entry used to say "when the mapping is
committed, `bd_mem` will need adding to `STORAGE_CELLS`". That is wrong, and
the station RTL is what settles it.** `slack.py` defers to the table today for
a good reason — the op was unbuilt and unaudited — but the deferral was hiding
the real question, and the answer goes the other way.

The checker's own criterion is in its module docstring: storage is what "lets
one side of a data cycle sit at rest while the other advances". That is slack —
capacity to hold a token while the producer moves on. The RAMB18E1 is the
strongest storage element in the library and it does not supply any, because
the capacity that matters is the STATION's, not the array's:

- The station holds `a_data` and `d_data` until `hold` rises, and `hold` rises
  on `z_ack` — the consumer taking the result. It cannot accept a new operand
  until its own output has been taken. Capacity zero.
- `hold` and `done` are both per-transaction, cleared when `joined` falls.
  Neither is long-lived, so neither is a token at rest. This is the same
  distinction section 6 already drew for `bd_ctree` against the arbiter's
  priority bit.
- The read data *is* registered — `DOADO` updates on the manufactured clock
  edge and holds — but that edge is manufactured from the request that is
  already going around the cycle. The register is downstream of the token, not
  a place the token can wait.

So a memory station is a compute unit with a RAM for a function, exactly as
this file's first sentence says, and compute units do not break rings. A cycle
closing through a `mem_controller` address echo will still be a real violation
after Stage 6, and the fix is a `bd_link` in that cycle — not a table edit.
Adding `bd_mem` to `STORAGE_CELLS` would make the checker bless a ring that can
deadlock, which is the failure `slack.py` exists to catch.

`STORAGE_CELLS` therefore needs no change when the mapping lands. What does
need writing is the mapping itself, and it should not be written until the port
has board evidence — see the entry below on what is and is not measured.

### Program order needs more than a token chain, and the bench says how much

With the release rule settled, the obvious next step is a program-order token,
and it costs almost nothing: `bdc/mem.py`'s `:seq` stations carry it as **one
more input to the existing join**, acknowledged by the same `hold`. No new
cell, no sequencer, and the token is released exactly when the operands are —
which is the rule proven above.

Chaining it is ordinary channel composition: a store's completion channel
carries no data, so `store.z -> load.c` is precisely a program-order edge.
(An earlier attempt wired the load's `c_req` from the store's `c_ack`. That is
not a handshake — an acknowledge is not a request — and the store's `hold`
falls on its own schedule, pulling the load's request out from under it
mid-join. Compose channels, not acknowledges.)

**It is not sufficient, and the shape of the failure is the point.** Offering
both accesses' operands at once and letting only the wiring order them
(`-DBDC_SEQ_TOKEN`):

| property | result |
|---|---|
| data ordering | correct, 0 failures |
| four-phase on the a channel | correct, 0 overlaps |
| port exclusivity | **violated, 12 times** |
| RAM edges vs accesses | **12 for 24** — half never happened |

One line of the station explains it: `z_req = p_ack & joined`. A station raises
its completion when the *port* acknowledges, which is while its own `p_req` is
still high — so the next station's token arrives before the port is free. A
completion channel means "my result is ready", not "I have let go of the
port", and program order across a shared port needs the second.

The load returned the correct value throughout. Not luck: `bd_mem` sets
`WRITE_MODE_A("WRITE_FIRST")`, so `DOADO` carries the data being *written* and
the load read the store's payload without ever performing a read. A bench
checking only data would have been green while half its accesses did not
occur.

So sharing one port between accesses is `bd_arbiter`'s job after all — the
library's own recommended answer, and section 1 already argues for arbitrating
unconditionally rather than building analyses to avoid it. This entry is the
measurement that says a cheaper answer was tried and does not work. The next
entry is what happened when the arbiter went in.

### The arbiter was necessary and not sufficient; the second gate is in the station

`bd_arbiter` drops onto the port exactly: the two slots are `r1/r2`, the RAM
gang is `R0/A0`, and the mux selects are `g1/g2`, which the cell's own header
establishes are exclusive by construction for a settled state node and — with
the `A0` hold — across handover too. So the caller's *obligation* becomes a
guarantee, and each slot gets its own acknowledge instead of a shared one.
`bdc_memport_arb_<AW>_<DW>_2` is that port. Two slots only; a tree for more
is not built, and the generator raises rather than guessing one.

**With the arbiter and nothing else, the token chain deadlocks: one RAM edge,
then nothing.** That is a cleaner failure than the previous one and a more
interesting cause.

`p_req = joined`, so a station claims the port for as long as its *operands*
are held — and the operands are held until its consumer is finished. When that
consumer is the next access on the same memory, the store will not free the
port until the load completes and the load cannot start until the store frees
it. The arbiter has nothing to arbitrate: neither request is illegal, and no
grant is wrong. A resource whose claim is scoped to the dataflow cannot be
shared with the dataflow.

The fix is two LUTs in the station, and it is not a delay:

```
done  = joined & (p_ack | done)     latched completion, gated by joined on
                                    BOTH terms so an idle station reads zero
                                    even while a shared p_ack is high
p_req = joined & ~done              the claim, dropped when the RAM answers
z_req = done                        was p_ack & joined — the same conjunction,
                                    latched, because p_ack now falls long
                                    before the consumer takes the result
```

The port then sees one four-phase transaction per access, bounded by the RAM,
with none of the surrounding dataflow inside it.

| | plain port | + arbiter | + arbiter + `done` |
|---|---|---|---|
| RAM edges / accesses | 12 / 24 | 1 / 24 | **24 / 24** |
| port exclusivity | violated 12× | held | **held** |
| four-phase on `a` | 0 overlaps | — (hung) | **0 overlaps** |
| load reads its store | yes, via `WRITE_FIRST` | — | **yes, on its own edge** |

The last row is why the edge count is the gate and the data is not. A
`WRITE_FIRST` read shares its write's clock edge; 24 accesses over 24 edges
are not sharing one, so the load performed a real read. Under the plain port
the data column was green while half the accesses did not happen.

Both failures are recorded rather than only the fix, because each was reached
by an argument that looked complete: "the token is released at port-quiet, so
program order composes" and "the grants are exclusive, so the port is safe to
share". Both are true. Neither is sufficient.

`tb/tb_bdc_memseq.v -DBDC_SEQ_TOKEN` is now a PASS. Three of that bench's four
modes are *supposed* to fail, which nothing ran until `verify/mem_modes.sh`
existed — a negative control nobody runs is not a control, and one that
quietly starts passing is worse than none. That script runs all four and is
red if EAGER passes or if the port's one-hot monitor stops firing, as loudly
as if the real modes break; it was checked by editing the fix back out of the
generated Verilog, where it correctly reported `BAD TOKEN` and exited 1.

The release-rule result above is unchanged: `-DBDC_SEQ_EAGER` still fails 12×
with 13 edges, and `done` makes that argument stronger rather than weaker,
since `p_ack` now falls even earlier relative to `a_ack`.

### The routed answer, and a hole in the sizing loop that is not about memory

`bdc/mem.py toparb:10:32` routes the arbitrated port for real — two RAMs, the
arbiter, both `:seq` stations — and it places, routes, and passes every gate.
`verify/tighten.py` needed no changes to handle it, and got the interesting
part right unprompted: rule B measured both the manufactured clock and the
latest payload from `uport.uarb.ustate$LUT6/O6`, the arbiter's state node,
which is the correct common launch for a path that now runs through a grant.

Then the sizing loop settled `UPORT_UMEM0_USETUP` at 5 links, on a route where
rule B had **10 ps** of margin against a 737 ps setup window.

Ten picoseconds is not a margin on this fabric, so it got re-routed:

| `USETUP` | routes | rule B on `umem0` |
|---|---|---|
| 5 (what resize settled on) | 5 seeds | **−108, −615, −719 ps, +10, +1081** — 3 violations |
| 8 (the untightened placeholder) | 6 seeds | +872 … +2405 ps, 12/12 ok |

So the size was not lucky, it was **wrong**, and nothing in the loop could have
said so. `flow.sh` is deterministic — no `--seed` — so "the candidate passed"
has always meant "the candidate passed on the one route nextpnr produces for
this netlist". A margin is a property of a route, not of a netlist.

`verify/resize.sh` already carried the right sentence about a different axis:
*any accept test that cannot observe the constraint a length was chosen for
will eventually undo that length.* This is the same sentence about routes.
`BD_RESIZE_SEEDS=N` now routes each candidate N times and keeps a size only if
all N pass; the proposal still comes from the unseeded route, so the loop's
answer stays reproducible and the extra routes only ever veto. Default is 1 —
N routes cost N times the place-and-route on every candidate of every sweep,
which is a real price — and at N=1 the loop now says out loud that its answer
holds on one route and no other.

**It helps and it is not enough, which is the part worth keeping.** At N=3 the
loop vetoed a shrink that N=1 had accepted — `UMEM1_USETUP` 8→7, killed by a
confirmation route at −719 ps — and settled on a genuinely different, larger
assignment. That assignment was then re-routed under eight seeds:

| | routes | rule B on `umem0` |
|---|---|---|
| N=3's answer (`USETUP` 5/8) | 8 seeds | −225, −266, −379 ps and five passes — **3 violations** |

Three confirmation routes are weak evidence against a defect that shows up on
roughly two routes in five: they all miss it about a fifth of the time, and
this time they did. Sampling is the wrong instrument here. The right one is a
guardband — rule A already has `max(0.2·t_data, 200 ps)` and rules B and C have
none, they compare against the vendor window bare — sized from the scatter,
which is measurable: at fixed lengths the manufactured clock's arrival moved
4325 → 5730 ps over six routes. That is about four delay links, which is the
entire tightening budget for this delay, and it says plainly that
`UMEM0_USETUP` should not be tightened here at all.

**Adding a guardband to rules B and C is a decision for the user, not for me.**
It would move every sizing result already on record, in the conservative
direction and at a throughput cost, and it is a change to the shared gate
rather than to anything memory owns. The measurement is here; the call is not
made.

**This is not a memory finding.** Every quoted margin from a single `flow.sh`
run is one sample, including the ones already on record. It showed up here
because the arbiter's mux lengthened the payload path enough to make the
scatter matter, but the scatter was always there: at fixed sizes the clock
arrival alone moved 4325 → 5730 ps across six seeds, which is roughly four
delay links — the entire tightening budget.

A caveat that cuts the other way, and is not resolved: a seed sweep is not a
PVT sweep. Six routes of the same netlist say how much the *router* moves; they
say nothing about temperature, voltage, or process, and the whole reason
shortening a matched delay is the risky direction is that silicon can be slower
than any of these numbers. `BD_RESIZE_SEEDS` narrows one source of optimism.
It does not make a tightened length safe.
