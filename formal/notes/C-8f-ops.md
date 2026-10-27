# C-8f: composition through Dynamatic's operators (track 8, Phase 3)

## Verdict

**Works.** A general composition theorem for handshake networks of bdc's
operators (any finite or infinite graph, cycles allowed) and gate-level
SI/DI models of `bd_fork`, `bd_join` (+ every compute unit), `bd_steer`
(`cond_br`) and `bd_mux`, each proved to meet the network's causal
assume-guarantee protocol spec and its token-level (Kahn) data spec. Core
Lean, no Mathlib, no `sorry`/`axiom`/`native_decide`. The mux invariant is a
132-state reachable set checked by kernel `decide +kernel` (no extra axiom;
`#print axioms mux_closed` prints none). About 1100 lines, ~3 h.

Not done: the gcd-shaped network assembled from these operators (see "Open"),
merge / control_merge (arbitrated: nondeterministic, needs an oracle stream),
the link with an initial token, source/sink/constant as proved cells (trivial),
liveness.

## Files

- `formal/lean/Formal/Net/Ops.lean`: offers, `Held` (H_BUNDLE), `Net`,
  `OpProto`, `OpData`, `net_protocol`, `net_refines`, `net_refines_close`,
  `net_determinate`; helper lemmas `rise_inv`, `close_val`, `held_at`,
  `open_offer`, `cnt_offers`.
- `formal/lean/Formal/Net/OpsFork.lean`: `Fork`, `fork_proto`, `fork_data`, `fork_op`.
- `formal/lean/Formal/Net/OpsJoin.lean`: `Join`, `join_proto`, `join_data`, `join_op`.
- `formal/lean/Formal/Net/OpsSteer.lean`: `Steer`, `steer_proto`, `steer_op`.
- `formal/lean/Formal/Net/OpsMux.lean`: `Mux`, `tbl`, `mux_closed`, `mux_guar`,
  `mux_inv`, `mux_proto`, `mux_op`.
- `formal/lean/Wip/C8f/mux_reach.py`: explicit-state reachability of the mux
  model (finds the 132 states and checks the counter differences are a function
  of the state); `-lean FILE` prints the Lean table. It proves nothing; Lean
  re-checks the closure.
- `formal/lean/Wip/C8f/MuxTest.lean`: the timing test of `decide +kernel` (scratch).

## Run

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    export LEAN_PATH=$PWD/.lake/build/lib/lean
    for f in Ops OpsFork OpsJoin OpsSteer OpsMux; do
      ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/$f.olean Formal/Net/$f.lean; done

Times: Ops 2 s, Fork 2 s, Join 3 s, Steer 12 s (Bool case splits), Mux 20 s
(kernel decide). Order matters (Ops first; Steer imports Fork). The lead must
add the five modules to `Formal.lean` and `check.sh` (I don't own them).

## The model

Time ℕ (1 tick = 1 ps), 8a's `Chan` (`req ack : Nat → Bool`, `dat : Nat → Nat`).

**Tokens are counted at the offer.** 8a names the k-th token by the k-th `ack↓`
(close). For combinational handshake operators that is backwards: a fork's
output token closes BEFORE its input token (the input ack waits for the
branches). At the offer (`req↑`), causality is forward and strict: every
output request rises strictly after the input requests it is made of, because
every gate and wire has delay ≥ 1 tick. So `OffAt c k r` = the k-th `req↑` is
the step r→r+1, the token's value is `c.dat (r+1)`, and `close_val` shows the
k-th close carries the same value under `Held`.

**H_BUNDLE (`Held c`)**: the bus does not change across a step that starts and
ends mid-transaction (phase ≠ 00). That is LIBRARY.md's "stable from req-rise to
ack-fall" with zero margins at the channel's wires; 8a's `SetupHold m h` (the
receiving latch's margins) sits on top for link inputs.

**Gate primitives (SI/DI, binary):**
- C-element / C-tree (H_CEL_SI, H_CTREE_ATOMIC): the output changes only to a
  value all inputs had one tick earlier (unbounded inertial delay). B's
  `CElemFn`/`CTree` justify the C-element under their timing conditions; the
  tree is lumped into one node here.
- LUT (H_LUT_SI): output changes only to the LUT function of the previous
  tick's inputs. Binary, no hazard model (B's mux-tree/Kleene probes cover
  hazards; for `bd_steer` the only moving data pin is `s`, and with `req = 0`
  both table entries along `s` are 0).
- Wire with fan-out (H_WIRE_DI): each sink gets its own unbounded inertial
  delay. The fork is NOT isochronic. Single-sink wires are lumped into the
  driving gate.
- Matched delay line (H_DELAY_LUMPED): lumped with its OR/C driver into one
  unbounded inertial node. Its LENGTH never matters for the protocol; it
  matters only for `Held` of the output channel (below).
- Data path (H_DATA_COMB / H_DATA_WIRE): the bus of each output is a function
  of the input buses at the same tick (zero delay). Every real data delay is
  pushed into `Held` of the channel it feeds. That is the fidelity gap, and it
  is exactly where track 10's checker plugs in.

Fidelity: the control model is speed independent (any gate delay) and delay
insensitive on fan-out wires, so it is MORE general than the fabric's bounded
delays in the control path. Its gaps: no runts/X/metastability (B's
Kleene/runt work), and the data path is ideal (covered by the H_BUNDLE
obligations, which are timing facts about routes).

## The general theorem (`Ops.lean`)

`Net C O`: operators `O` with input/output channel lists; each channel has one
producer and one consumer operator (the environment is operators too).

- `OpProto ch ins outs`: causal AG: if all touched channels started in reset,
  the inputs are bundled (`Held`), and both protocol rules held on every
  touched channel at all steps `< t`, the operator obeys its own rules at `t`.
- `net_protocol`: every channel obeys the four-phase protocol (strong induction
  on time; any graph).
- `Eqs`: each operator's token equations `E o : (C → Nat → Nat) → Prop`.
- `OpData ch ins outs E`: (given protocol + `Held` on its channels) the value of
  the operator's k-th output token offered at r equals `σ c k` for EVERY
  stream assignment `σ` that agrees with the circuit on all tokens offered
  before r and satisfies `E`.
- `net_refines`: all operators meet `OpProto` + `OpData`, every channel meets
  `Held` ⇒ for every solution `ref` of all the equations, every offered token on
  every channel has value `ref c k`; `net_refines_close`: so does every closed
  (latched) token. At every time, each channel's sequence of values is a prefix
  of the token semantics' sequence.
- `net_determinate`: two solutions agree on everything the circuit offers.

**Why "every cycle passes through a link" is not a hypothesis.** Safety needs
only strict causality in time, which every operator spec provides. A cycle with
no storage cannot hold a token, so it deadlocks (liveness: 9's three-stage
rule); safety then holds vacuously. If some operator were modelled with zero
delay (a pure rename), the induction would need an extra rank on the
zero-delay subgraph, and the acyclicity of renames would be the condition.
bdc's pure renames (`br`, `constant`, `trunci`/`extui`/`extsi`, 1-input `merge`)
should be eliminated by identifying channels (their token equation is the
identity / a map), not modelled as operators.

## Per-operator results

| op (bdc lowering) | model | token equations | theorems |
|---|---|---|---|
| fork, lazy_fork (`bd_fork`) | DI req wires, ack C-tree | `σ oᵢ k = σ a k` (duplicates) | `fork_proto`, `fork_data`, `fork_op` |
| join (`bd_join`), compute units `addi subi muli andi ori xori shli shrsi shrui cmpi select` (`bd_join`+logic+`bd_delay`), cond_br's join | req C-tree (+ lumped delay), DI ack wires, `o.dat = g(in buses)` | `σ o k = g [σ i₁ k, …, σ iₙ k]` (pairs / applies) | `join_proto`, `join_data`, `join_op` |
| cond_br (`bd_join`+`bd_steer`) | two LUT nodes, OR node | input token i goes to branch b = sel(σ j i) as that branch's token #{i'<i : sel(σ j i') = b} (routes) | `steer_proto`, `steer_op` |
| mux 2-way (`bd_mux`) | j0/j1/xa/ya C-nodes, lumped OR+delay, DI ctl_ack | `σ z k = if sel(σ c k) then σ y (#1s before k) else σ x (#0s before k)` (selects; unselected token stays) | `mux_closed`, `mux_proto`, `mux_op` |

Proof technique: fork/join/steer by hand-written per-branch Boolean invariants
(`FInv`, `JInv`, `SInv`) checked by `decide` plus count invariants
(#req↑ in = #req↑ out + [state-dependent correction]). The mux by a computed
reachable set: Python finds 132 states; Lean's kernel checks closure under every
gate/environment step, the four protocol guarantees, the counter updates and
the facts at a z-offer.

Notable facts the proofs exposed:
- The steer and the mux are the only operators whose PROTOCOL correctness
  needs data bundling (`Held` of the select channel): if `s` moves mid
  transaction, the steer can raise the other branch. Hence `OpProto` takes
  `Held` of inputs.
- `bd_mux`'s `x_ack` can stay high across the NEXT control token (it waits for
  `z_ack↓` of a later y transaction); the model allows it and nothing breaks:
  132 states, no protocol violation, and the counters stay within ±1.
- `bd_snk` (`ack = req` wire) violates 8a's `RecvStep` if the wire has zero
  delay (both wires move in one step). With a DI wire (≥ 1 tick) it is fine.

## Timing obligations (form for track 10)

Each is a property of one channel's route; all are `Held`-type
(data-before-request) unless stated. For the checker: "path P1 (data) settles
before path P2 (request) arrives, for every delay in the band", i.e. a two-path
race like 8e's `race2_sound`.

| id | where | statement (named delays, worst case over the corner band) |
|---|---|---|
| H_BUNDLE(c) | every channel c | `dat` of c stable from the step after `req↑` until after `ack↓` (zero margins at the consumer's pins) |
| H_COMPUTE_DELAY(u) | compute unit u output | max(operand bus → logic → `z_data` pin of every consumer) < min(last operand req → C-tree → `uor` → `udly` → `z_req` pin of every consumer) ; and the output bus holds until `ack↓`: min(ack↓ → operand senders release → logic → z_data) > 0 relative to the consumer's close (8a `Hold`) |
| H_STEER_SEL(b) | cond_br b | max(cond bus → `s` pin of the steer LUT) < min(cond req, data req → join C → steer `req` pin) (select before request at the steer LUT itself; bdc's `SELECT_PAD`) |
| H_STEER_DATA(b) | cond_br b branch k | data bus → branch consumer's data pins settles before steer LUT → branch req pin |
| H_MUX_SEL(m) | mux m | max(ctl bus → `s` pins of j0/j1 LUTs) < min(ctl_req → j0/j1 `ctl_req` pin) (the link feeding a select has DELAY = SELECT_PAD for exactly this) |
| H_MUX_DATA(m) | mux m output | max(s → datamux → z_data at consumers, and x/y data → datamux → z_data) < min(j0/j1 → uor → udly → z_req at consumers) |
| H_FORK_DATA(f) | fork f branch i | data wire to branch i's consumer settles before the req wire to it (the req fan-out is a wire, so this is a pure route skew obligation; DI req wires make no protocol obligation) |
| H_FORK_ACK | fork | none: the C-tree completion is DI in the model (any per-leaf ack delay). Only B's per-C-element conditions (H_QFB_FIRST etc.) remain |
| H_JOIN_TWO_REQ | join | none for the protocol (C-tree waits for both); for data: each operand's bus must be valid at the consumer before z_req, i.e. it is H_COMPUTE_DELAY with the max over ALL operands (bundling across two requests) |
| H_LINK (8a) | link | `Sep`, `Hold`, `SetupHold` as in C-8a |

## Open

1. **The gcd-shaped network** (8b's `KahnGcd.G`) assembled from these
   operators: needs an initial-token buffer for the loop's select tokens (8b's
   `init` store has `[0]` on `sA`/`sB`; bdc gets the first select from the
   arbitrated control_merge instead) and a token-level lemma that every
   solution of the gcd equations has `out 0 = gcd a b`. Est. 0.5-1 day.
2. **control_merge / merge** (`bdc_amerge` = arbiter cascade + bd_mux):
   nondeterministic. Plan: treat the index output as an oracle stream (any
   value the arbiter picks); data spec relative to it. Determinacy then holds
   only modulo the oracle, and the gcd proof needs 8b-CM's "one control token in
   flight" invariant at token level. Est. 1 day.
3. Link with an initial token, source/constant/sink as proved cells: small.
4. N-way mux tree (`bdc_muxn`, gcd's 3-way header): compose 2-way muxes with a
   decoded select; the reachable-set method should scale (or prove per level).
5. Liveness of networks (8a has it for pipelines).

## What it buys the project

- A machine-checked reduction of "the network computes the token semantics" to
  local facts: each cell meets its spec (proved here for fork, join/compute,
  steer, mux in the SI/DI model) plus one data-before-request obligation per
  channel (H_BUNDLE), which is what rules A/E/J approximate and what track 10's
  checker should discharge per route.
- It shows which cells need data timing for their HANDSHAKE (steer, mux: the
  select) and which need none (fork, join): the select channels are exactly
  bdc's `select_channels()`, which is where the silicon deadlocks were.
