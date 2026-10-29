# C-O4b: generated-cell binding for every kernel; H_LEAF_PERSIST and H_REQ_PERSIST discharged

Shard C, probe O4b (track 8 / goal 3), 2026-10-29. Core Lean only (no Mathlib), no
sorry/axiom/native_decide. Builds on O4 (`notes/C-O4-cells.md`, `Formal/Net/CellBind*.lean`)
and 8y2 (`notes/C-8y2-generic.md`, `Formal/Net/KernelCap*.lean`).

## Verdict

- **Generic binding: works, for all four kernels.** `CellBind.K.kernel_circuit_safe_gen` is
  8y2's `kernel_circuit_safe` (any kernel `[KD] [KP]`) with H_GEN (every operator obeys its
  yosys-generated netlist, `GenCellK`) in place of H_CELLS. Instances with the statements of
  the four H_CELLS theorems: `gcd_hw_circuit_safe_genK`, `ipow_circuit_safe_gen`,
  `collatz_circuit_safe_gen`, `xorshift_circuit_safe_gen`.
- **One operator kind O4 did not cover: the 3-input compute unit** (ipow op 20, collatz op 16:
  `bd_join #(.N(3))`). O4's `GenCell` is `False` on it, so O4's H_GEN is UNSATISFIABLE on ipow
  and collatz (`ipow_O4_vacuous`, `collatz_O4_vacuous`, proved): restating with it would have
  been vacuous. Fixed with a newly generated netlist `bd_join_N3` (gen.sh's yosys flow,
  `Wip/CO4b/gen_extra.sh` → `CellBindKNets.lean`); its LUT is the 3-input C-element
  (`j3_gate`). Kernel-checked census (`*_shape`): every operator of all four networks has a
  covered width (forks 2..6, compute joins 1..3, branch joins 2). ipow's DSP-backed `muli`
  is a compute unit's DATA path (copied hypothesis H_DATA_COMB, as before); its request side
  is the ordinary bd_join + `uor` + delay, so nothing new is needed there.
- **H_LEAF_PERSIST and H_REQ_PERSIST are discharged, no counterexample.**
  `CellBind.PersistK.kernel_circuit_safe_genP` (and four instances `*_genP`) assume
  `GenCellKP` = `GenCellK` with BOTH hypotheses removed (fork N = 5, 6 trees, compute joins
  N = 2, 3, mux and muxN joins; bd_link `rdly`, bd_mux `udly`). They follow from the four-phase
  protocol by a joint induction on time with the protocol derivation (`cells_of_genP`): the
  persistence at tick `s` comes from the operator's EXISTING reachable-state invariant at `s`
  (C-8f/8l: `fork_inv`, `join_inv`, `mux_inv`, `muxn_inv`, `link_inv`, applied to the run
  frozen at `s`, which needs the lumped field only before `s`) plus one kernel-decided fact
  per kind about that invariant.
- **Still hypotheses** (unchanged from O4): H_LUT_SI, H_FB_FIRST, H_PIN_EQ, H_CHAIN_SETTLED
  (a genuine timing condition, O4's `fastfall_hazard`), H_WIRE_DI, data / select / arbiter /
  latch fields, H_MUXN_OR, H_R0_ISO, H_PORT_ORDER, reset values; plus H_BUNDLE, H_START_ONCE.
- **Non-vacuity: quiet only, three of four kernels** (`*_gen_witness`, `*_genP_witness`):
  gcd_hw (8t, 12/18), collatz (n = 7), xorshift (seed 2463534242, rounds 4) runs frozen at
  tick 0 satisfy the full hypothesis set jointly. ipow: no `Cell` run exists in `Formal` to
  freeze (open). No active whole-network run satisfying H_GEN (open, as in O4).

## Run

    cd /home/user/asyncfpga3/formal
    ./check.sh Formal/Net/CellBindKNets.lean Formal/Net/CellBindKOps.lean Formal/Net/CellBindK.lean \
               Formal/Net/CellBindPersist.lean Formal/Net/CellBindPersistOps.lean \
               Formal/Net/CellBindPersistMux.lean Formal/Net/CellBindPersistK.lean
    ./slot.sh lake env lean Wip/CO4b/MutantJ3.lean    # MUST fail (negative control)
    ./slot.sh lake env lean Wip/CO4b/Shape.lean       # census of operator widths (#eval)
    lean/Wip/CO4b/gen_extra.sh                         # regenerates CellBindKNets.lean (needs yosys)

Result 2026-10-29: `[audit] 6488 declarations checked`, `[check] OK` (about 2 min on one slot;
`CellBindPersistMux` is the slow one, ~90 s, the muxN table `decide`s).

The lead must add to `Formal.lean` (I do not own it), in this order, after O4's six modules
(`CellBind`, `CellBindNets`, `CellBindChain`, `CellBindOps`, `CellBindGcd`, `CellBindWit`, which
are also not yet in `Formal.lean`): `CellBindKNets`, `CellBindKOps`, `CellBindK`,
`CellBindPersist`, `CellBindPersistOps`, `CellBindPersistMux`, `CellBindPersistK`. Other
dependencies (existing oleans): `KernelCapGcd/Ipow/Collatz/Xorshift`, `KernelCapSafe`,
`XorshiftWit`, `CollatzWit`, `OpsFork/Join/Mux/MuxNOp/Link`.

## Files

| file | contents |
|---|---|
| `Formal/Net/CellBindKNets.lean` | GENERATED (`Wip/CO4b/gen_extra.sh`, gen.sh's flow): `bd_join_N3`. Not covered by `gen.sh --check` |
| `Formal/Net/CellBindKOps.lean` | `j3F`/`j3_gate`; `JoinNodeK`, `GenJoinK`, `join_of_genK` (compute unit N = 1..3); **`GenCellK`, `cell_of_genK`**; `shapeK`, `gen_frozenK` |
| `Formal/Net/CellBindK.lean` | **`kernel_circuit_safe_gen`** + 4 instances; `*_shape` (kernel decide); `genCell_join3_false`, **`ipow_O4_vacuous`, `collatz_O4_vacuous`**; `gcd/collatz/xorshift_gen_witness` |
| `Formal/Net/CellBindPersist.lean` | freezing (`fz`, `fzC`, `fzK`, transfer lemmas); causal lumping `cel_inv_upto`, `cel_lumped_upto`, `or_inv_upto`, `or_lumped_upto`, `bufchain_lumped_upto`; `GenBufChainP`; `cell_proto'`; **`opproto_of`** |
| `Formal/Net/CellBindPersistOps.lean` | `finv_leaf`, `jinv_leaf`, `link_leaf` (decide); `ForkTreeP`/`GenForkP` + **`fork_core`**; `GenJoinKP` + **`join_core`**; `GenLinkP` + **`link_core`**; `*_fz`, `*_all`; `fork_needs_protocol` |
| `Formal/Net/CellBindPersistMux.lean` | `mux_leaf0/1`, `muxn_leaf` (decide over C-8l's encoded table); `GenMuxP` + **`mux_core`**; `GenMuxNP` + **`muxn_core`** |
| `Formal/Net/CellBindPersistK.lean` | `GenCellKP`, `genP_of`, `op_proto`, `op_cell`, **`cells_of_genP`**, **`kernel_circuit_safe_genP`** + 4 instances, `*_genP_witness` |
| `Wip/CO4b/gen_extra.sh`, `Wip/CO4b/json/bd_join_N3.json` | generator of CellBindKNets (copy of O4's, N = 3 of bd_join) |
| `Wip/CO4b/MutantJ3.lean` | negative control, must NOT check (INIT bit 1 of bd_join N = 3 flipped: `decide` proves the gate lemma false) |
| `Wip/CO4b/Shape.lean`, `Wip/CO4b/Tables.lean` | exploration: width census per kernel (`#eval`), first check of the table facts |

## Part 1: the generic binding

```
theorem kernel_circuit_safe_gen [KD] [KP] (a b : Nat) (hd : dom a b) (ch : Fin NC → Chan)
    (H_GEN : ∀ o : Fin NO, GenCellK ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = spec a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (spec a b))
```

`GenCellK` is O4's `GenCell` except on `.join`, where it uses `GenJoinK` (bd_join N = 1, 2, 3
→ `uor` → request delay with H_CHAIN_SETTLED). `cell_of_genK : GenCellK → Cell` (all K kinds).

Census (`Wip/CO4b/Shape.lean`, kernel-checked as `ops.all shapeK = true`):

| kernel | forks | compute joins | other kinds |
|---|---|---|---|
| gcd_hw (367 ops) | 2, 3, 4, 5, 6 | 1, 2 | bjoin 2, steerC/D, mux, muxn, amerge, link, src, sink |
| ipow (83) | 2, 3, 4 | 1, 2, **3** | bjoin 2, steerC/D, mux, amerge, link, src, sink |
| collatz (66) | 2, 3, 4 | 1, 2, **3** | same |
| xorshift (77) | 2, 3, 4 | 1, 2 | same |

So beyond the 3-input compute unit, every kind and width the other kernels use is one O4
already bound for gcd_hw. The muxN cell occurs only in gcd_hw.

## Part 2: the joint induction

The circle O4 left: the capstone derives the protocol from the lumped Ops fields (`Cell`), and
the lumped field of a two-level C-tree / C-element-before-delay / OR-before-delay / plain delay
chain needs persistence, which only the protocol provides.

How it is broken (all in Lean):

1. **Freezing** (`fzC T`): every trace holds its tick-`T` value from `T` on. A one-step field
   holds vacuously at steps `≥ T`, so "field at steps `< T`" builds the Ops structure of the
   frozen run, and every existing invariant / `OpProto` applies to it; conclusions at ticks
   `≤ T` transfer back. O4's `cel_inv`, `or_inv`, `buf_chain` become causal the same way.
2. **Per kind, a core lemma** (`fork_core`, `join_core`, `mux_core`, `muxn_core`, `link_core`):
   if the operator's channels obeyed the protocol before `T`, its lumped field holds at every
   step `≤ T`. Strong induction on the step `u`: the persistence needed at `s < u` comes from
   the existing invariant at `s` (run frozen at `s`: needs the field only before `s`, the
   induction hypothesis) plus a decided fact:
   - fork (`finv_leaf`): in C-8f's `FInv`, a branch ack that the receiver may move
     (`ack ≠ req`) equals the fork's ack;
   - compute join (`jinv_leaf`): in `JInv`, an input request the sender may move (`req = ack`)
     equals the joined request;
   - mux (`mux_leaf0/1`) and muxN (`muxn_leaf`): in C-8f's 132-state / C-8l's encoded table, a
     join C-element that is excited already equals `z_req`; `uor` then moves only when `z_req`
     shows it (from `or_inv_upto`), which is `udly`'s end-only persistence;
   - link (`link_leaf`): in C-8l's 18-state table, whenever the controller `c` is excited,
     `req_out = c`: `rdly`'s end-only persistence.
3. **`opproto_of`**: the core lemma at `T` builds the `Cell` of the run frozen at `T + 1`;
   `cell_proto` on it gives the operator's guarantee at `T`, so the operator is a causal
   `OpProto` operator of the real run (`op_proto`). `net_protocol` (unchanged) then gives the
   protocol on every channel, and the core lemmas at every `T` give the lumped fields at every
   tick (`op_cell`), i.e. H_CELLS (`cells_of_genP`).

`fork_needs_protocol`: O4's `tree_needs_persist` run is a `GenForkP` fork whose lumped field
fails (its leaf withdraws while its request never rose); so the protocol premise is used, not
decorative. Nothing analogous to `fastfall_hazard` exists for these two hypotheses: in the
four-phase protocol they cannot fail.

What the persistence discharge does NOT cover: H_CHAIN_SETTLED (side-tapped chains, bd_link's
`uack`) is a different, timing condition and stays; the rig theorem (`gcd_rig_all_gen`, O4) was
not restated with `GenCellKP` (it does not go through `net_protocol` in the same form; not
attempted).

## Hypotheses of `kernel_circuit_safe_genP` and non-vacuity

| hypothesis | where | status |
|---|---|---|
| H_LUT_SI + H_FB_FIRST (`CNode`, `LutSI`) | every LUT | quiet witness; active single cells: O4 |
| H_PIN_EQ | convention (non-feedback pins read the net's trace) | as O4 |
| H_CHAIN_SETTLED (`GenChain`) | uack, compute / muxN / amerge request delays | quiet witness; real condition (`fastfall_hazard`) |
| H_WIRE_DI | fork req_out, join ack_out, mux/muxN ctl_ack, sink | quiet witness |
| data / select / latch / arbiter fields, H_MUXN_OR, H_R0_ISO, H_PORT_ORDER, reset (incl. internal nodes start equal to the node they feed) | per field | quiet witness |
| H_BUNDLE, H_START_ONCE | network | quiet witness |
| ~~H_LEAF_PERSIST~~, ~~H_REQ_PERSIST~~ | | **proved** (`cells_of_genP`) |
| joint | gcd_hw / collatz / xorshift | `*_genP_witness` (quiet); ipow: none (open) |

## Not done / open

- An active whole-network witness for H_GEN (any kernel); an ipow witness of any kind.
- `gcd_rig_all` with `GenCellKP`.
- `bd_join_N3` (like O4's `CellBindNets`) is outside `gen.sh --check`; the lead may prefer
  adding it to `formal/tools/gen/targets.txt`.
- H_CHAIN_SETTLED as a tcheck row (O4's open item, untouched).
