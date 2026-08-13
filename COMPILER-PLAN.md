# Building the compiler on top of the cell library

Stage 0 is done: `cells/` is a bundled-data primitive library that routes on a
Zynq 7010, costs what it says it costs, and is held up by seven gates. This is
the plan for the thing that emits designs made of it.

The founding decision stands — **rebuild, do not fork Dynamatic**. Not one line
of Dynamatic is patched or inherited. Its buffer-placement MILP in particular
does not survive the move: it optimises against a clock period, and there is no
clock.

**Revised 2026-08-12: do Stage 7 first.** "Rebuild" was being read as "write a
frontend too", and that is not what it has to mean. Stage 7 below already names
the cheap path — consume CIRCT/Dynamatic's `handshake` output *as data*, which
keeps the rebuild decision intact. Doing that first rather than last changes
what the remaining stages are:

- `--handshake-materialize` guarantees "every SSA value is used exactly once by
  inserting forks and sinks as needed". That is the one-producer/one-consumer
  channel discipline Stage 1 was going to define, for free and already tested.
- The cut is immediately **above `--handshake-place-buffers`**, the single pass
  that assumes a clock. Everything upstream is protocol-agnostic dataflow.
- Their backend is already table-driven — `data/rtl-config-verilog.json` maps 96
  `handshake.*` ops onto HDL. A bundled-data backend is that table with a
  different library behind it.
- Their *RTL library* does not transfer at all: `data/verilog/handshake/fork.v`
  has `clk`, `rst`, `ins_valid`, `ins_ready`. Synchronous elastic. The dataflow
  graph transfers; the timing does not, and neither do guarantees stated in
  cycles. See `bdc/AUDIT.md`, which records each one that was checked.

What remains genuinely ours is the backend, the compute units (Stage 3), and
slack (Stage 5). Stages 4, 6 and 7 largely stop being work.

---

## The rule that carries over from Stage 0

Everything below is subordinate to one thing: **a generated design is held to
exactly the standard a hand-written one is.** The seven gates do not get an
exemption for being machine-produced. Concretely that means the first milestone
is not a language or an IR — it is making `verify/soak_top.v` a *generated*
file, so that from the very first commit the compiler's output is going through
`inits.py`, `lutcost.py`, both simulation regimes, `flow.sh`, `tighten.py` and
`teeth.sh`.

Four more, inherited verbatim:

- Every matched delay is a **placeholder**. `tighten.py` runs unconditionally
  after place-and-route. A delay that must *grow* is a bundling violation, not
  a sizing result.
- Nothing claims a number it has not measured.
- Negative results go to `attempts/` **with the bench that reproduces them**.
- Cost claims are measured the way `lutcost.py` measures them, never asserted.

---

## Stage 1 — netlist IR, emitter, generated soak

The smallest thing that makes every later stage gateable.

**IR.** Two concepts only. A *channel* is a bundle `{req, ack, data[W]}` with
exactly one producer and one consumer. A *node* is an instance of a library cell
or a generated unit, with named channel ports. That is all — no types, no
regions, no dialect. The graph is the program.

**Emitter.** Walk the graph, emit Verilog instantiating `rtl/` cells, emit a
`sizes.vh` of delay placeholders keyed the way `BD_SZ_*` already is.

**Gate.** Regenerate the soak design from a graph description and require the
full `check.sh` to pass on it. The existing hand-written `soak_top.v` becomes
the reference the generator must reproduce.

Deliverable: `./check.sh` green on a generated top.

---

## Stage 2 — the node set, and what each lowers to

| Dataflow node | Cells | Note |
|---|---|---|
| fork | `bd_fork` (+`bd_ctree` past fan-out 4) | data is wires; the cost is the ack rendezvous |
| join | `bd_join` | the dual |
| conditional branch | `bd_steer` | + `bd_bd2dr` **only** if the condition arrives on its own channel |
| merge, inputs exclusive | `bd_merge` | caller must discharge exclusivity |
| merge, inputs **not** exclusive | `bd_arbiter #(HOLD_ON_ACK(1))` + `bd_merge` | this is where Finding 2 pays for itself |
| mux (select is data) | `bd_mux` | |
| buffer / register | `bd_link`, `bd_pipe` | |
| load / store | `bd_mem` | one port, manufactured clock edge |
| **compute unit** | *does not exist yet* | Stage 3 |

Note the converter rule the library already states: bundled everywhere,
dual-rail only on control channels that arrive separately from the data they
steer. When the condition rides in the bundle there is no boundary and no
converter — so most branches cost a `bd_steer` and nothing else.

**Gate.** Each mapping gets a bench in the shape of the existing ones, run in
both timing regimes.

---

## Stage 3 — the compute cell generator (highest risk, do it early)

This is the one genuinely new cell class, and the first time yosys-optimised
logic sits *inside* a bundled-data unit.

A compute unit is: data through ordinary combinational logic, `ack` straight
through, and `req_out = Δ(req_in)` where Δ is a matched delay covering the
logic's own critical path. The Δ discipline is already exactly this — "a matched
delay covers combinational logic inside one cell's own datapath" — so nothing
conceptual is new. What is new is that the logic is *generated*, so its depth is
unknown until routed.

Two concrete problems to solve:

1. **The delay is unknowable at emit time**, which is fine — emit a placeholder
   and let `tighten.py` size it. That is what the pass is for.
2. **`tighten.py` has to find the cell boundary.** It currently anchors rule A
   on a `<cell>.uor` request OR, a convention that only holds for hand-written
   cells. Generated units need a declared boundary — a wrapper module plus an
   attribute the SDF preserves — and rule A's `confine` has to key off it.
   This is a real change to the sizing pass, not a naming exercise: `confine`
   is the definition of the check, not an optimisation, and getting it wrong
   turns every line in the design into a violation.

Prototype end to end with **one** unit — an 8-bit adder — before generalising.

---

## Stage 4 — control flow

- SSA φ → `bd_mux` when the selector is available as data; `bd_merge` when the
  predecessors are provably exclusive.
- Branch → `bd_steer`.
- Loops → **the standing invariant: exactly one token inside the loop, and the
  buffer comes from the loop body, not from the steer.**

**Gate.** A token-conservation checker over the graph: tokens in equal tokens
out for every construct, and — separately — **every cycle contains at least one
storage stage**. The second is a correctness property, not a performance one:
a cycle with no storage is a combinational loop, and no amount of routing makes
it work.

---

## Stage 5 — slack, and why it is not Dynamatic's buffer problem

Dynamatic places buffers by MILP to hit a clock period. There is no clock, so
that formulation has nothing to optimise against. Two separate obligations
replace it:

**Correctness.** Every cycle needs ≥1 storage stage. This is an exact graph
property, checkable, and it is not negotiable. Do this first and completely.

**Throughput.** A four-phase pipe's cycle is a full round trip, and the simple
controller holds one token per *two* stages. Adding stages costs area and
latency and buys concurrency. With no clock to meet, this is a pure trade —
so **measure it on hardware, do not model it.** Start with "one storage stage
per cycle, plus one per long combinational run", get programs running, and only
then look at whether optimisation is worth anything.

This is also the one place the decoupled controller would matter: one token per
stage instead of one per two, at 2 LUTs of control plus `W/2` of latch, which
beats the simple controller per token stored from `W = 2` upward. That is why
`attempts/bd_deco_attempt.v` is worth resolving eventually. It is not on the
critical path and should not block anything.

---

## Stage 6 — memory ordering

`bd_mem` is a single port. Real programs need ordering between accesses, which
is the piece Dynamatic spends an LSQ on.

Recommend **program-order serialisation first**: thread a token chain through
memory operations in program order, one `bd_mem` port, correct by construction
and slow. It is enough to run end-to-end programs, which is what unblocks
everything else. An LSQ is a large independent project and should be started
only once there is something to measure it against.

---

## Stage 7 — frontend (deferred, as decided)

Interim input is a hand-written graph in the Stage 1 format. If a real frontend
is wanted later, the cheap path is a converter from CIRCT's `handshake` MLIR
into the Stage 1 IR — consuming its *output* as data, which keeps the rebuild
decision intact and avoids re-deriving a C frontend.

---

## What the library still lacks

Small, and worth knowing before Stage 2 starts:

- a compute-unit wrapper (Stage 3)
- ~~a constant source and a sink~~ — `bd_src` / `bd_snk` in `rtl/bd_end.v`.
  `req = ~ack` and `ack = req`; one LUT and free respectively, both measured.
  Two things the compiler has to know about them: a `bd_src` must sit behind a
  consumer that resets, because it has no state of its own to reset and `~x`
  is `x`; and its inverter folds into whatever consumes `req`, which is a
  Stage 2 peephole worth about one LUT per constant.
- a token source for loop initialisation — *not* `bd_src`, which offers
  forever. A loop needs exactly one token, once.
- an N-way distribute, if `bd_steer` chains prove too deep

---

## Suggested order

1. **Stage 1**, ending at a generated `soak_top` that passes `check.sh`.
2. **Stage 3 prototype** — one 8-bit adder, end to end, including the
   `tighten.py` boundary change. This is where the unknown-unknowns are.
3. **Stage 2** proper, one node at a time with a bench each.
4. **Stage 4 + the cycle checker.**
5. **Stage 6** serialised memory, then a real program end to end on the
   EBAZ4205.
6. Everything else.

The reason for that order: step 2 is the only part where I do not already know
the shape of the answer, and it is cheaper to find that out against one adder
than against a compiler.
