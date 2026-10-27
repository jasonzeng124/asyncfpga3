# B-fork-data: H_FORK_DATA (row C14) and H_AMERGE_IDX (row C11)

Probe Bfd, shard B. Lean: `formal/lean/Formal/Cells/ForkData.lean` (core Lean,
imports `Bundling`, `AMergeTimedW`). Check:
`scratchpad/bchk.sh formal/lean/Formal/Cells/ForkData.lean` -> `[bchk] OK`.
Axioms: only propext / Classical.choice / Quot.sound (`#print axioms` on
every theorem below). Draft cell_constraints entries (not merged):
`<scratchpad>/Bfd/draft_entries.py` and `.json` (3 entries; they pass
`cell_constraints.validate.py` on a merged scratch copy, except the expected
"untracked file" errors).

## 1. What bdc emits

`bd_fork` (cells/rtl/bd_ctl.v): `req_out = {N{req}}` (a wire fan-out),
`ack = bd_ctree(ack_in)`. `emit.py _op_fork`: `assign o_k_data = x_data` for
every branch. So the data bus is ONE net with one route per branch, and the
fork has no forward gate. Its forward obligation is only the bundling of each
branch at its consumer's pins. control_merge emits `bdc_amerge` + `bd_fork _f`
(index and result leave together through a fork).

Census (gcd_hw re-emitted with the pads build, read-only use of bdc, output in
scratch; 139 branches over all `bd_fork` in `bdc_gcd`): 53 end at
`bd_link`/`bd_pipe` (a latch captures the branch data), 59 at `bd_join` (data
goes on to a steer select or a compute unit), 12 at a nested fork, 6 at
`bd_snk`, 9 are control-only. `BD_LINK_DC` is not defined, so every latch
consumer is a Muller link: `bd_c2n` node = enable, transparent from the node's
rise to its fall.

## 2. H_FORK_DATA, stated at the consumer's pins

Per branch B (Nat ps, Bundling's window model): `dhi` = shared data driver ->
this branch's route -> latch D pin -> output; `fhi` = latch loop (incl. the I2
arc); `rlo` = producer req -> fork wire -> `bd_c2n` -> node rise (min);
`elo/ehi` = node -> EN pin -> output; `wlo` = node rise -> node fall (min):
DACK, fork C-tree, producer, req fall, fork wire; `alo` = node fall ->
producer's next data change (min).

- **H_FORK_DATA** (C-8f's wording, "data before req"): `Td + dhi + fhi <= Tr + rlo + elo`.
- **H_FORK_DATA_W** (the exact form): `Td + dhi + fhi <= Tr + rlo + wlo + elo`.
  This is `bd_latch.setup_data` (L1) with the launch at the fork's producer.
- Side conditions: H_FORK_PULSE `ehi + fhi <= wlo + elo` (L2), H_FORK_HOLD
  `ehi <= alo + dlo` (L3 with the fork's C-tree on the ack path).

| theorem | statement (assumed / proved / NOT covered) |
|---|---|
| `branch_capture` | Assumed: BrRun (LatchRel of the real INIT over windows, H_LOOP_POS, clean enable pulse, data `v` on [Td, Tnew), H_REQ_LO, H_EN_WIDTH, H_REL_LO), H_FORK_DATA_W, H_FORK_PULSE, H_FORK_HOLD. Proved: `q = v` on `[max(Ton+ehi, Td+dhi), Tnext+elo)`. Via `Bundling.capture`. |
| `fork_capture` | The same for every branch `i : ι` of one fork, ONE shared data net `d`, per-branch windows and request paths. |
| `edge_implies_W` | H_FORK_DATA => H_FORK_DATA_W. |
| `fork_data_needed` | Necessity, parametric: every branch with point windows (transport, admitted by `transport_gate`), `1 <= flo`, `1 <= Td`, H_FORK_PULSE, and `Td+dhi+fhi = Tr+rlo+wlo+elo+1` (violated by exactly 1 ps) has a trace of the REAL odd-bit LUT6 INIT, satisfying every BrRun field at the minimal environment for every Tnext/Tnew, where `q = !v` at the closing instant `Toff+elo` and every `fhi` after it (the stale value circulates). The instant lies inside branch_capture's interval. |
| `fork_data_needed_num` | The hypotheses are satisfiable (D 400, EN 300, loop 150, req 200, round trip 900, Td 851). |
| `fork_data_good` | Non-vacuity, parametric: every point-window branch meeting H_FORK_DATA_W + PULSE (and `1 <= Tr+rlo`) has a BrRun where q really goes `!v` -> `v`. |
| `edge_form_not_needed` | H_FORK_DATA fails by 850 ps, H_FORK_DATA_W holds, the latch captures. |

NOT covered: the LUT6_2 pair bits in the counter-trace (sufficiency covers them
through `pair_o5_latch`/`pair_o6_latch`); the 59 join-consumer branches (their
data obligation becomes the join consumer's: H_STEER_SEL / rule E, or the
compute unit's rule A, end to end through the fork wire); nested forks are
pass-through (apply at the leaf); no routed number; the C-tree/ack path is
only a lower bound `wlo`, `alo` (environment).

Finding (exactness of the row as written): C-8f's "data wire settles before the
req wire" is sufficient but NOT necessary at every latch consumer gcd_hw has.
The exact obligation has the handshake round trip as credit, which is what
rule I already computes (`t_close = t_rise + t_ack + t_fall`, tighten.py
~1850). So C14 is not "no rule": for link -> fork -> link branches it is
rule I (with rule I's known missing I2 arc, `bd_latch.setup_data`
missing_term). Producers that are not link stages (amerge index, compute,
steer/mux outputs) are "not audited" by rule I. That reading is of the code
only; I did not see a routed tighten log (none in the repo).

## 3. C11: H_AMERGE_IDX

gcd_hw's control_merges are all `bdc_amerge2_0`/`bdc_amerge3_0` (width 0):
`in_k_data(1'b0)`, `.z_data()` unconnected. The data-mux leg is therefore
constant (`amerge_data_const`); the whole obligation is the index. Cm2
(`AMergeTimed`) already has the three races in arc form. This file names their
conjunction:

- `H_AMERGE_IDX D W cmin := BidxA ∧ BidxB ∧ IdxAckFork`.
- `amerge_idx_sufficient` (with the arbiter's RT2b): the consumer reads the new
  owner (1, resp. 0) from `su` before the capture, every run of the real
  arbiter, every server, every capture instant allowed by H_REQ_PATH; the
  index stays 1 while in1_ack is high.
- `amerge_idx_necessary`: the exact legs: `¬BidxA` (with A0Fork, H_Z_IN_SRV)
  -> previous owner at the minimal request path; `¬BidxB.ack` at a consistent
  corner -> stale 1; `¬IdxAckFork` with the minimal client -> index 0 while
  in1_ack is high. `BidxB.gack` is sufficient only; `BidxB.grant` has its own
  counter-trace (`bidx_old_owner_counter_g`).
- `amerge_idx_nonvacuous`: SLOW_MAX, DELAY 12, `cmin = 248`: all of it plus
  RT2b hold (runs in `AMergeTimedW.nonvacuous_slow`).

NOT covered: amerge3's index[1] and race 2 (as in Cm2); a routed instance.

Finding for C11 (links to C14): Cm2's consumer samples at the request edge
(index settled `su` before `Zr`). In gcd_hw every index goes through the `_f`
fork (and sometimes a second fork, e.g. `ucontrol_merge2 -> ufork9`) into
Muller `bd_link`/`bd_pipe` stages, which close a whole handshake after `Zr`.
So the Cm2 counter-traces show a stale index at the request edge, not a stale
latched value. At these consumers the exact condition is H_FORK_DATA_W with
`Td` = index settle time. Cm2's legs are sufficient there, not necessary.

## 4. Draft entries (scratch, not merged)

`bd_fork.branch_data` (H_FORK_DATA_W, sufficient+necessary, rule I
missing_term), `bd_fork.branch_data_edge` (H_FORK_DATA as written,
sufficient), `bdc_amerge.idx_bundle` (H_AMERGE_IDX, the conjunction plus the
consumer caveat).
