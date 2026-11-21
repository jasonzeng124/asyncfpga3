# C-8a: handshake-network composition (track 8, protocol level)

## Verdict

**Works.** Safety (protocol on every link + FIFO/prefix of values) and liveness
of an n-stage four-phase bundled-data pipeline are proved in core Lean, for an
abstract assume-guarantee stage spec AND for a concrete Muller stage built on
the real `bd_c2n` INIT. The data correctness of internal links reduces to two
control-only per-link timing obligations (`Sep`, `Hold`) plus the latch's cell
contract, which is the form track 10's checker needs. About 1000 lines,
~2 h of work. No `sorry`, `admit`, `axiom` or `native_decide`.
`#print axioms` on every main theorem gives only `propext`, `Classical.choice`
and `Quot.sound`.

## Files

- `formal/lean/Formal/Net/Handshake.lean`: channel and protocol definitions,
  bundling, abstract `StageSpec`, `Pipeline`, composition theorems.
- `formal/lean/Formal/Net/HandshakeMuller.lean`: the Muller stage
  (`bd_link`, default build) in two gate models, its stage spec, the
  internal-link reduction, the Muller pipeline theorem.
- `formal/lean/Formal/Net/HandshakeLive.lean`: liveness.
- `formal/lean/Formal/Net/HandshakeWitness.lean`: a concrete one-token run that
  satisfies every hypothesis of `muller_pipeline`, so the theorem is not
  vacuous.
- `formal/lean/Wip/C8a/Axioms.lean`: `#print axioms` script. It proves nothing.

Imports: `Formal.Net.Prelim` (traces) and `Formal.Cells.Prelim` (`lutB`). No
Mathlib.

## Run

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    export LEAN_PATH=$PWD/.lake/build/lib/lean
    for f in Handshake HandshakeMuller HandshakeLive HandshakeWitness; do
      ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/$f.olean Formal/Net/$f.lean; done
    ../slot.sh lean Wip/C8a/Axioms.lean

Each file takes about 1 to 2 s. They must be compiled in this order, because
each one imports the previous. The lead has to add the four modules to the root
`Formal.lean` and to `check.sh`, since I don't own those files.

## Definitions (Handshake.lean)

- `Chan`: `req ack : Trace`, `dat : Nat → Nat` (the bus read as a number).
- `SendStep c t`: `req` moves at step t → `req t = ack t`.
  `RecvStep c t`: `ack` moves → `ack t ≠ req t`.
  `Init`: both are low at 0. `Protocol = Init ∧ ∀ t, SendStep ∧ RecvStep`.
  `phase_step` proves that these rules are exactly the 4-cycle
  `req↑ ack↑ req↓ ack↓`: no phase is skipped, the two wires never move in the
  same step, and a new request never comes before ack↓ (`req_rise_ack_low`).
- Token: `TokAt c k e`: the k-th `ack↓` happens at step e. The token's value is
  `c.dat e`, the bus at the close, which is what a latch consumer keeps.
- `Bundled m h c` is the LIBRARY.md form: data stable from `m` ticks before
  `req↑` until `h` ticks after the matching `ack↓`.
  **Decision:** the brief said "until ack↑", but LIBRARY.md and the bd_link
  header both say the window must end at **ack↓**, because the latch is still
  transparent until then. I followed the library. A window that ends at ack↑
  does not give `SetupHold` at the close.
- `SetupHold m h c` is what a transparent-latch consumer actually needs:
  data stable on `[e+1-m, e+h]` around each close `e`.
  `bundled_setupHold`: `Bundled m' h` + `OpenWidth w` (each close is at least
  w after its req↑, a control-only fact) + `m ≤ m' + w` gives `SetupHold m h`.
  So the classic form is sufficient, but it is not the needed form.
- `StageSpec m h i o` (assume-guarantee):
  `ag`: if both links obey both rules at every step `< t`, the stage obeys
  `RecvStep i` and `SendStep o` at step t. This is causal: the premise covers
  strictly earlier steps.
  `initIn`/`initOut`: reset leaves `ack_in` and `req_out` low.
  `xfer`: Protocol on both links + `SetupHold m h i` → `Transfers i o`. The
  k-th token out was the k-th token in, closed strictly earlier, with the same
  value.

## Theorems proved

| theorem | statement |
|---|---|
| `phase_step` | the two rules give exactly the 4-phase order |
| `falls_inv` | count invariant: #req↓ = #ack↓ + [req=0 ∧ ack=1] |
| `bundled_setupHold` | classic bundling + open width → latch setup/hold |
| `transfers_trans`, `transfers_count` | composition; #tokens out ≤ #tokens in |
| `pipeline_protocol` | n stages meeting `StageSpec` + a causal source and sink → every link obeys `Protocol` |
| `pipeline_fifo` / `pipeline_prefix` | + `H_LINK_SETUP_HOLD` on links 0..n-1 → FIFO: the k-th output token = the k-th input token (index form of "output sequence is a prefix of the input sequence"), and the counts satisfy out ≤ in at all times |
| `celN_eq` | real `bd_c2n` INIT `00B2…` = C(req_in, ¬ack_out) |
| `muller_stageSpec` | Muller stage (speed-independent model) ⊨ `StageSpec` |
| `mullerW_stageSpec`, `mullerW_pipeline_protocol` | the same with a 1-tick wire delay on both controller input pins |
| `node_latch_transfers` | the data half needs only node identity + latch contract |
| `muller_hold1` | `Hold 1` is free in the SI model |
| `muller_out_setupHold` | input `SetupHold` + `Sep m'` + `Hold h'` → output `SetupHold m' h'` |
| `muller_pipeline` | n Muller stages: Protocol on all links + FIFO, from the source's `SetupHold` plus `Sep`/`Hold` on the internal links only |
| `muller_live` | + fairness/environment liveness → every link's ack changes infinitely often, and the sink gets unboundedly many tokens |
| `Witness.witness` | a one-token run (value 42) satisfying all hypotheses of `muller_pipeline` |

## Is assume-guarantee composition circular? How it was broken

**Yes, in general.** Stage k's receiver guarantee on its input link needs
stage k-1's sender rule there: a request withdrawn before the controller saw
it would make the controller move against the protocol. Stage k-1's sender
guarantee needs stage k's receiver rule, and so on around the loop. Taking
each spec as plain implication "env OK → I am OK" is unsound for such loops.

**How it was broken:** the stage spec is *causal*. A guarantee at step t uses
the assumptions only at steps `< t`. `pipeline_protocol` is then a strong
induction on time over all links at once. This is the standard
Misra–Chandy / Abadi–Lamport fix. It is sound because every physical gate has
a strictly positive delay.

**What the concrete models show:**
- In the speed-independent atomic-gate model (`MullerStage`: zero wire delay,
  arbitrary gate delay), the protocol guarantees are *combinational
  invariants*. From `cel_change`, the node moves only when `req_in ≠ c` and
  `ack_out = c`, so `muller_stageSpec` never uses the assumption, and the
  circularity is vacuous.
- With a 1-tick wire on the controller's input pins (`MullerStageW`), the
  proof of the step-(t+1) guarantee uses `SendStep`/`RecvStep` of **both** links
  at step t. That includes the stage's own earlier guarantee, which is why
  `ag`'s premise includes all four rules. The circularity is real there, and
  the time induction is what resolves it.
- Not done: a general per-tick-varying wire delay `≤ D`. It needs the same
  argument over a D-step window ("no req change in the last D steps"), which I
  expect to cost about half a day.

## Per-link timing obligations (what feeds track 10)

For `bd_pipe` (Muller stages, `DELAY = DACK = 0`), `muller_pipeline` needs:

1. **Input link (environment), data:** `H_SRC_SETUP_HOLD = SetupHold m h (ch 0)`:
   source data stable on `[e+1-m, e+h]` around every close e of link 0.
   `bundled_setupHold` turns it into the LIBRARY.md bundling plus an
   open-width check.
2. **Each internal link j+1 (between stages j and j+1), control only:**
   - `Sep m (ch j) (ch (j+1))`: the downstream close (c_{j+1}↓) comes at least
     m ticks after the upstream close (c_j↓) it follows. In bd_pipe this is the
     controller arc + `SDELAY` vs the latch setup (**rule I**). It is exactly
     the "closing wave gains on the data wave" failure from LIBRARY.md
     (tb_link latched X into stage 2).
   - `Hold h (ch j) (ch (j+1))`: the upstream node does not reopen within h
     ticks of the downstream close (**rule H / DACK**). `h = 1` is free
     (`muller_hold1`).
   Neither one mentions data. A checker over control-path delay intervals can
   discharge both.
3. **Cell contract (per stage, from shard B):** `H_LATCH m h`: a latch closed at
   e, with its data stable on `[e+1-m, e+h]`, holds `d e` until it reopens.
   This is B's `holds_value_bin` (`Formal/Cells/Latch.lean`) with m ≥ the loop
   delay L. **The bridge is not mechanised**, because B works per bit in `K3`
   and here the value is a whole-bus `Nat`. Lumping W bits under one enable
   needs the enable fan-out skew (DACK, ~1 ns at 32 bits) inside h.
4. **Output link (sink):** only the protocol (`snk`) is required. The
   theorem's conclusion gives values at the sink's close steps. A sink that
   samples at `req↑` (BRAM, edge-sampling) is NOT covered: req_out leads data
   by one latch arc per stage (LIBRARY.md, 152/441 ps). It needs its own
   obligation of the `Bundled` form at that boundary (the `DELAY` line).

`Sep` is conservative. It asks the downstream close to come m after the
upstream *close*, while the real requirement is m after the upstream data
*settles*, which can be earlier while the latch is transparent. That costs some
slack, and soundness is unaffected.

## Liveness: exactly what it needs (`muller_live`)

The safety model allows "never move", so liveness needs three extra
hypotheses:
- `H_SRC_LIVE`: an infinite source. When it is its turn (`req = ack` on link 0),
  it eventually moves `req`.
- `H_SNK_LIVE`: an always-ready sink. When `ack ≠ req` on link n, it eventually
  moves `ack`.
- `H_CEL_FAIR`: every excited C-element eventually changes. This is the
  liveness half of H_BOUNDED_DELAY (`settle`); `H_CEL_SI` is the safety half.
No data or timing hypotheses are needed: liveness is purely a control
property. The proof has three steps: (1) req and ack changes alternate on a
protocol channel, so one stopped wire stops its partner (`stops_of`); (2) every
node is the ack of one link and the req of the next, so one stopped wire stops
all of them; (3) `deadlock_free`: no static state has nothing excited. The
result is qualitative: it gives no throughput or latency bound. A bounded
version (each move within D) is a straightforward strengthening that has not
been done.

## Fidelity of the primitive models used

- **Time:** ℕ ticks (1 ps), as in Net/Prelim. Fine for safety. Edges between
  ticks are atomic.
- **C-element (`H_CEL_SI`):** the real INIT `64'h00B2_00B2_00B2_00B2` through
  `Cells.Prelim.lutB`, binary, with `rst = 0` after reset. At each step the
  node either keeps its value or takes its function value (unbounded inertial
  delay). This holds for every gate delay. It does not cover runts, X or
  metastability; for those, see shard B's `CElemTiming` and the Kleene probes.
  The feedback-loop internals are abstracted into the node. B shows the loop
  behaves as a C-element under its timing conditions.
- **Wires:** `MullerStage` uses zero wire delay and an **isochronic fork** on c
  (`H_NODE`: req_out, ack_in and the latch enable are one signal). This is
  unfaithful: the routed fork has different wire delays, often hundreds of ps.
  `MullerStageW` adds a 1-tick delay on the controller's input pins, but the
  fork itself is still isochronic. Test: SDF INTERCONNECT on net c, comparing
  the delays to its sinks.
- **Latch (`H_LATCH`):** an abstract cell contract, discharged per bit by shard
  B with the real INIT and a bounded loop delay. Bus lumping is an extra
  assumption.
- **Environment:** an abstract causal source and sink.
- **Matched delays `DELAY`/`SDELAY`/`DACK`:** not modelled as cells. They enter
  only through `Sep`/`Hold`, which are the properties they exist to establish.

## Not done / open

- The bridge from B's `holds_value_bin` (K3, per bit, at the pins) to
  `H_LATCH` (bus, at the node): about 0.5 to 1 day, mostly type plumbing plus
  an enable-skew hypothesis.
- A general bounded wire delay (≤ D, varying per tick) on all pins, including
  a non-isochronic fork on c: about 1 day. The fork version is the interesting
  one. With skew between ack_in and the latch enable, the sender may release
  data before the latch closes. That is DACK, and it should come out as a
  `Hold` obligation.
- Forks, joins, merges, muxes (non-linear networks): the `StageSpec`/time
  induction carries over (the induction is over a finite set of links), but
  `Transfers` needs a per-channel token-index map. That is the bridge to probe
  8b's Kahn semantics.
- A list-valued "prefix" statement: the theorem is stated in index form, which
  is equivalent. Adding `List.IsPrefix` is cosmetic.
- No ring (initial tokens): the latch carries no token at reset. That is
  probe 9.

## What it buys the project

- A machine-checked statement of what "the pipe is correct" depends on:
  exactly one data obligation at the input and two control-only separations
  per internal link, plus the cell contracts. That is the specification
  rules H and I should check. A checker proved sound against `Sep`/`Hold`
  (track 10) would make those rules exact, not heuristic.
- The tb_link X failure is explained formally: it is a `Sep` violation, and no
  rule checked `Sep` before `SDELAY` was added.
- The circularity question is settled: it is harmless with atomic gates, real
  with wire delays, and resolved by causal assume-guarantee with induction on
  time.
