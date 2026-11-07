# B-reset-capstone: B's gcd_hw reset theorems connected to C's circuit capstone

Probe Brz (shard B), 2026-10-29. It connects B's reset results (`ResetGcd`,
`ResetGcdVec2`, on Rst2's elaborated-RTL control network `gNet`) to C's
capstone (`gcd_hw_circuit_safe3`, on C's 465-channel operator network).

No route, no board, no toolchain run. `gNet` is the bdc-emitted RTL with
default sizes plus `gcd_rig`. It is not a routed netlist. Every time below is
a model step.

## Files and check

All three files check, with no `sorry`, `admit`, `axiom`, `native_decide` or
`extern`. `formal/scan.py` passes on them. Each was checked with
`/tmp/claude-0/btools/bcheck.py Formal/Cells/<file>`, which printed OK.

- `formal/lean/Formal/Cells/ResetCapstoneGlue.lean` (828 lines). Imports
  `Formal.Net.CapstoneNetChk`, read-only. Covers parts (1) and (3) below:
  C's initial-state content, `AtS`, the glue, and `CellA`.
- `formal/lean/Formal/Cells/ResetCapstoneWit.lean` (280 lines). Imports
  `ResetGcdVec2`. Holds the non-degenerate witness run of `gNet`.
- `formal/lean/Formal/Cells/ResetCapstone.lean` (580 lines). Imports the two
  files above, plus `Formal.Net.CapstoneWalk` and `Formal.Net.CapstoneWitness3`
  (both read-only). Holds the mismatch, the reset-state bridge, the headlines
  and the non-vacuity witnesses.

`#print axioms` was run in a scratch file, which was then deleted:
- `cap_idle0`, `nonvac_net2` and `wit_wire_lag` depend on propext and
  Quot.sound only.
- Every other headline depends on propext, Classical.choice and Quot.sound.

The lead still has to add the three files to `Formal.lean`.

## (1) What C's capstone assumes at time 0

There is no separate reset hypothesis. The assumption sits in the `init*`
fields of each operator's gate model inside `H_CELLS`:

| C model | fields at time 0 |
|---|---|
| `Fork.Fork` | `initA` (input ack 0), `initO` (output reqs 0) |
| `Join.Join` | `initO`, `initI` |
| `Steer.Steer` | `initJ`, `initO` |
| `Mux.Mux` | `i0`, `i1` (joins `j0`, `j1`), `iz`, `ix`, `iy`, `ic` |
| `MuxN.MuxN` | `ij`, `iz`, `ix`, `ic` |
| `CM.AMerge` | `i1`, `i2` (grants), `iz`, `ix`, `iy` |
| `Link.Link` | `ic` (C-element `c`), `ii`, `io` |
| `Capstone.Src` | `iz` (a, b and start are NOT offered at time 0) |
| `Gcd.Sink` | `init` |

`cap_idle0` proves the consequence. Every channel has a producer and a
consumer (C's `prod_mem` and `cons_mem`), so `H_CELLS` implies
`Handshake.Init` (req = ack = 0) at time 0 for all 465 channels. Every
internal node is also 0 at time 0. Data is unconstrained. This is C's row
H_RESET ("every channel starts at req = ack = 0 and every C-element node at
0"). C's network has no initial tokens.

`gcd_hw_live_final` uses `CellI`, which carries the same `init*` content. I
did not redo the glue for `CellI`.

## (2) The mismatch: the RTL never reaches C's initial state

**Negative result.** `rtl_env_high` covers every bounded GMW run of `gNet`
with rst held on `(0, E]`. Two nodes are 1 at every step of
`[23(D+W+1), E]`:
- node 3275, `urig.uenv1`: the rig token, a `bd_c2n_set`;
- node 3257, `urig.upsnk.g[1]`: the p_end acknowledge.

`rtl_env_high_release` extends this past release, until a frontier link
moves.

`rtl_not_idle`: suppose start's request is read from node 3275. Then no shift
`T0` in that window satisfies C's `H_CELLS`, because `Src.iz` already fails.
C's literal H_RESET is therefore false for the RTL.

**The RTL state in C's channel terms (`AtS`).**
- The requests of channels 0..6 are 1:
  - 0 = a, 1 = b, 2 = start;
  - 3 = `0#0` (p_end), 4 = `0#1`, 5 = `1#0`, 6 = `1#1`.

  All of them are wires of uenv1.
- Channel 3's acknowledge is 1: upsnk has already consumed.
- Every other wire is 0, and so is every internal node.

`hot_wiring` (by `rfl`) gives the `gNet` pins that identify these channels:
- `ucond_br9_j`, `ucond_br10_j` and `ucond_br11_j` read node 3275 at pin 0, as
  the data requests of b, `0#1` and `1#0`;
- the controller `ulink_n1__1` reads it as its request;
- `upsnk` is a two-element buffer from it;
- `ufork0`, the ack C-element of the start fork, reads upsnk.

B's census `gcd_reset_ones` lists the only control nodes that are 1 at reset:
- rst;
- the 9 arbiter priority states `ustate.O6`;
- the 4 `bd_src`;
- upsnk g[0] and g[1];
- uenv1.

The arbiter q is not a wire of C's `AMerge`, which has only grants. The
`bd_src` channels do not exist in C's network: C-8i collapsed them under
H_SOURCE_ETERNAL.

**Per cell type: B's reset value against C's init field.** In the table,
"rv" is B's certified reset value of the node.

| cell (RTL) | B's node and reset value | C field | holds? |
|---|---|---|---|
| bd_link | ctl `bd_c2n` rv 0 (`gcd_links_empty'`); uack/rdly chains flush to 0 | `Link.ic/ii/io` | yes, all 175 links (no link output is hot: `side_chk`) |
| fork | ack C-element (`bd_c2/c3/c4`) rv 0; output reqs are wires of the input req | `initA` / `initO` | `initA` yes; `initO` **no** for forks 0 (start) and 1 (a): outputs 3..6 are 1 |
| join, bjoin | C-element rv 0; input acks are wires | `initO`, `initI` | yes |
| steer | O5/O6 = AND(join, sel) and uack OR, both stateless, 0 | `initJ`, `initO` | yes |
| mux, muxn3 | uj0/uj1 rv 0, uor 0 | `i0`, `i1`, `ij`, `iz`, ... | yes |
| amerge (bd_arbiter) | ugrant O5/O6 rv 0 (q = 1 is not a C wire) | `i1`, `i2`, `iz`, ... | yes |
| src a/b/start | wires of uenv1, rv 1 | `Src.iz` | **no**: req = 1 |
| sink p_end | upsnk rv 1 | `Sink.init` (ch 3) | **no**: ack = 1 |
| other sinks | ack = req wire, 0 | `Sink.init` | yes |
| bd_src (4) | rv 1 | none (collapsed in C) | n/a |

Every internal node of C's models is a control node that is not in `onesL`.
`rtl_cold_node` proves each such node is 0 at `T0`.

`gcd_reset_vec_net` (Bfw) is about `exc`, the LUT value a gate sees. The
channel state needs output values, so the bridge uses `gcd_reset_binary`
(Rst2), which gives every control node's output on `[23(D+W+1), E]`.

## (3) The bridge

**The glue (`gl r T0`).** It runs three virtual C-legal ticks from C's idle
state, then continues as the real family `r` from `T0` on:
- tick 1: the sources rise;
- tick 2: the fork branches rise;
- tick 3 (the junction with `r` at `T0`): the sink acknowledges.

In the prefix, the data is `r`'s data at `T0`.

**`CellA` (H_CELLS_AFTER).** These are C's gate models with the `init*`
fields dropped and every step field restricted to `t ≥ T0`. The operator's
internal nodes must be 0 at `T0`. The fields are restated per kind:
`ForkA`, `JoinA`, `SteerA`, `MuxA`, `MuxNA`, `AMergeA`, `LinkA`, `SrcA`,
`SinkA`.

`glue_cell` proves the glue one cell type at a time: `glue_fork`,
`glue_join`, `glue_steer`, `glue_mux`, `glue_muxn`, `glue_amerge`,
`glue_link`, `glue_src` and `glue_sink`. Each one needs a decidable side
condition, `Side`, which says which wires the prefix moves.
`side_chk : ops.all Side = true` decides it for all 367 operators.

`glue_cells` concludes: if `AtS r T0` holds and `CellA` holds for every
operator, then C's `H_CELLS` holds for `gl r T0`.

**Theorems.**
- `gcd_hw_safe_from_reset` (C side). Assume, for `a, b < 2^31`:
  - `AtS r T0`;
  - `CellA` for every operator;
  - `HeldA`: H_BUNDLE from `T0` on;
  - no start request rise after `T0`.

  Then every `out0` acknowledge fall at or after `T0` carries
  `Nat.gcd a b`. The proof applies `gcd_hw_circuit_safe3` to the glued
  family.
- `atS_of_rtl` (B to C). Take a channel map `μ` (request node and
  acknowledge node per channel) that satisfies `MapOK`:
  - each mapped node is a control node other than rst;
  - a node is in `onesL` exactly for the 7 hot requests and for channel 3's
    acknowledge.

  If `r`'s wires at `T0` equal `v T0 ∘ μ`, then `AtS r T0` holds for every
  `T0` in `[23(D+W+1), E]`.
- **Headline: `gcd_hw_safe_after_reset`.** Hypotheses:
  - `Rn`: a GMW run of `gNet`;
  - `hB`: Bounded `D` `W`;
  - H_RST_HELD: rst held on `(0, E]`;
  - H_HOLD_LONG': `T0 ≤ E`;
  - H_MAP and H_MAP_T0;
  - H_CELLS_AFTER;
  - H_BUNDLE_AFTER;
  - H_START_AFTER.

  `T0 = T0of D W = 23(D+W+1)` is explicit. Conclusion: every `out0` latch
  at or after `T0` carries `Nat.gcd a b`.

## (4) Non-degenerate witness for Bfw's network theorem

`ResetCapstoneWit.nonvac_net2` gives a bounded GMW run `wRun` of the real
`gNet` (all 3322 nodes, real INITs). Parameters:
- `D = 40`, `W = 1`;
- `F = 967`, so H_HOLD_LONG is tight: `23·42 + 1 = 967`;
- `E = 1007`.

H_STEER_HOLD constrains the six steer outputs on the six steps
`(1001, 1007]`; it is no longer vacuous.

The run:
- power-up is the reset state;
- every pin reads its source one step late before `E` (`wit_wire_lag`);
- every gate holds until `E`;
- after `E`, the unit-delay simulation takes over.

It is a GMW run because the reset state is a binary fixed point of every LUT
with rst = 1 and data 0. `fix_ok` decides this over all 3322 nodes, in 9
chunks.

`wit_frontier_held` shows that the gate bound is really used. The controller
of `ulink_n1__1` (node 1696) sees LUT value 1 at every step of `[F+2, E]`,
and still shows 0.

The file also applies `gcd_reset_vec_net` to this run, with nothing
per-cell supplied.

This is the slow extreme: every gate uses its whole delay budget. No run with
intermediate delays was built.

## Non-vacuity of the headlines

- `reset_capstone_nonvac` meets every hypothesis of `gcd_hw_safe_after_reset`
  jointly, with:
  - `wRun` (`D = 40`, `W = 1`, `E = 967`, `T0 = 966`);
  - the map `μW` (hot requests from 3275, channel 3's acknowledge from 3257,
    everything else from the cold node 65), checked by kernel decide;
  - the frozen family `frzC chW` (`AtS` forever, with C's 8t time-0 data).

  On this family nothing moves after `T0`, so the conclusion is vacuous.
- `gcd_hw_safe_from_reset_nonvac` meets every hypothesis of the C-side
  theorem with C's 8t run `chW` seen from `T0 = 2`, and out0 latches 6 there.
  `chW` at time 2 is in `AtS`, with channel 3's acknowledge still 0; `AtS`
  leaves that acknowledge free.
  - `cell_restrict2` turns C's `Cell` into `CellA _ 2`. The internal nodes
    are still 0 at time 2 because no input of a link, mux or arbiter requests
    at times 0 or 1; this is decided on `chW`.
- No single witness runs both models. They are different models, joined only
  by H_MAP at `T0`.

## Exactly where the two models disagree

1. **Initial tokens.** C assumes "all channels idle at 0". The RTL holds the
   rig's token offered on a, b and start (and their fork branches) during
   reset, and the p_end sink has already consumed it. Bridged by the 3-tick
   virtual prefix: the RTL state is C-reachable from C's idle state.
2. **Time and rst.** C's models have no rst. They start at time 0 with
   `rst = 0` in `ctlB`. The RTL is quiet but under rst on `[T0, E]`. Because
   C's relations only say "if it moves, it moves to f(previous)", a constant
   wire meets them, and B proves every mapped wire constant there. But
   H_CELLS_AFTER is still a hypothesis.
3. **Wires.** C has one trace per wire. In GMW each reading pin sees the
   driver with its own lag (≤ W). H_MAP identifies C's wire with the driver's
   output, and the reader skew stays inside C's SI/DI gate hypotheses (O4).
4. **Constant sources.** C has none (H_SOURCE_ETERNAL). In the RTL, 4
   `bd_src` are 1 at reset and 9 of the 10 frontier links fill from them
   after release.
5. **Per-cell versus network.** `gcd_reset_vec_net` is about `exc`. The
   bridge needs output values, which `gcd_reset_binary` gives.

## Not covered (open)

- **The channel map table.** H_MAP, `MapOK`. No mechanised map exists from
  C's channel names (GcdHw SSA value + link segment) to `gNet` node ids. Only
  the hot neighbourhood is evidenced (`hot_wiring`). Building it means
  regenerating Rst2's lost generator with net names, then checking `MapOK` by
  decide.
- **H_CELLS_AFTER from B's GMW run.** This is C's O4 refinement (C's SI
  models versus bounded GMW gates; it needs excitation persistence). It is
  not attempted here.
- **H_START_AFTER.** It inherits the H_START_ONCE caveat: the rig re-offers
  start after each result. The per-result version (8s2) is not glued.
- **Liveness.** `gcd_hw_live_final` and its `CellI`, `BndG`, `StartEnv` and
  `ArbUnc` are not glued.
- **The source frontier links.** Their effect on the joins they feed (an
  extra C-element input that C does not model) is not covered.

## Proposed JOURNAL-B paragraph

Brz (ResetCapstone, ResetCapstoneGlue, ResetCapstoneWit) connects B's reset
to C's capstone.
- C's initial state is the `init*` fields of H_CELLS. `cap_idle0`: all 465
  channels are idle and every internal node is 0 at time 0.
- The RTL never reaches that state: uenv1 and upsnk are 1 on
  `[23(D+W+1), E]` (`rtl_not_idle`).
- The RTL reset state `AtS` (requests 1 on channels 0..6, channel 3 acked)
  is C-reachable in 3 virtual ticks. `glue_cells` proves this per cell type,
  with `side_chk` decided for all 367 operators.
- `gcd_hw_safe_after_reset`: B's GMW reset, plus a channel map (H_MAP,
  `MapOK`), plus C's gate models, bundling and start from
  `T0 = 23(D+W+1)` on, give gcd on every out0 latch from `T0`.
- Witnesses:
  - joint: `wRun` with `D = 40`, `W = 1`;
  - C side with a result: `chW` from `T0 = 2`;
  - `nonvac_net2` replaces the degenerate `D = W = 0` witness, and
    H_STEER_HOLD is now live on 6 steps.
- Open: the map table, H_CELLS_AFTER from GMW (O4), liveness, the
  `bd_src` frontier.
