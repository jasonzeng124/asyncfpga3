# B-contract-bridge: IpowCells' contract fields from B's own theorems

Probe Bbr (shard B), 2026-10-29. One new Lean file, `formal/lean/Formal/Cells/ContractBridge.lean`
(about 910 lines, core only: imports `IpowCells`, `CTreeExact`, `ArbPin`). Checked with
`/tmp/claude-0/btools/bcheck.py Formal/Cells/ContractBridge.lean`, result `OK`, no warnings. No sorry,
admit, axiom or native_decide. The lead must add `Formal.Cells.ContractBridge` to `Formal.lean`.
The LutFb / H_LUT_SI bridge is probe Bfb's (`LutFbBridge.lean`) and is not touched here.

## 1. What each field became

| IpowCells field (where used) | B theorem used | B hypotheses that replace it | result |
|---|---|---|---|
| **H_CTREE_ATOMIC** (`JoinC.req = FbCel cgate ..` at arity 5, op 20 `uselect0`) | `CTreeExact.tree_suff` (the sufficient half of `tree_box_exact`), `iv_phase`, `arrive_bound`, `anc_bound` | `CTreeB`: B's tree model (per-node H_PIN_READ, monotone read maps in the box, H_LEAF, H_ACK, feedback maps in the box), **H_CTREE_LOOP** (`Cond`), H_LO_POS (every read lower bound >= 1 ps), H_RUN (every finite prefix of the run is a prefix of one B-model run) | **derived exactly as stated**: `fbCel_of_ctreeB` gives `FbCel cgate xs o`; `ctreeB_cel` gives C's `Join.cel` step. Any tree shape; `leaves5`/`sh5` for ipow, `leaves6`/`sh6` for gcd_hw's N=6 fork |
| **H_SEL_PIN**, steer (`SteerC.H_LUT_SI`, 8 steers) | `LibGapSteer.steer_tokens` | `SelPin`: H_REQ_TOK, H_S_STABLE, H_SETUP_PIN (`S0 k + ps.hi <= R k + 1`), H_HOLD_PIN (`F k + 1 <= S1 k + ps.lo`), with the request read through C's one tick (`Rd.const 1`); H_SEL_DEC (bus decodes to `v k` during token `k`); B's H_PIN_READ for the two outputs (level form, real INIT) | **derived exactly as stated** (`steer_lut_of_pins`, in level form, hence in change form). H_SEL_DEC itself follows from C's H_BUNDLE when the request is high on the whole token window (`sel_dec_of_held`) |
| **H_SEL_PIN**, mux (`MuxC.uj0/uj1 = FbCel .. sel (c.dat t)`) | `steer_tokens` (pin-generic) | `uj0`/`uj1` = `FbCel` on the PHYSICAL select pin `s (ps.σ (t+1))` + `SelPin` | **derived exactly as stated** (`muxC_of_muxB`): `uj0_of_pin` gives LutFb + FbFirst on the decode, `fbCel_iff_si` turns it into `FbCel` |
| **H_DELAY_LUMPED**, mux (`MuxC.H_DELAY_LUMPED : LutSI muxZF ..`, uor + `bd_delay`) | B's per-pin read map (`LibGapSteer.Rd`), H_PIN_FIFO (`NecessityMerge.Mono`), `NecessityMerge.exists_change` | `ReqPath`: the path is ONE read map (H_OR_SAME_PATH: both uor pins on one map), monotone, lo >= 1, and **H_PULSE_WIDTH** (`Width r.hi`: after each change the OR's input holds for the path's max delay) | **derived exactly as stated** (`lumped_of_fifo`, `muxC_of_muxB`). **Counter-run** `lumped_needs_fifo`: with a NON-monotone map in [1,3] (allowed by LibGapDelay's H_PIN_READ) and one clean input step, `z` goes 1, 0, 1 and changes to 0 at 12 while the input was 1 at 11: H_PULSE_WIDTH holds, the field fails. So the field needs FIFO reads (GcdCells' model), not LibGapDelay's box |
| H_DELAY_LUMPED, gated (fused join `z_req`, amerge `ustate.O5 -> bd_delay_gated`) | none | none | **open**. The field lumps TWO SI nodes (C-element or `ustate.O5`, then the gated line) into one node at one tick. The line alone is a FIFO lumped node by the same argument as `lumped_of_fifo` (not written for the AND chain), but the composite also needs the inputs to wait for `z` (an H_ACK-type hypothesis that LibGapDelay/GcdCells do not have) |
| **H_ARB_EXCL** (`AMergeC`, 2 arbiters) | `ArbPin.su_osc_instance`, `ArbPin.su_box_iff` | — | **not derivable as stated**: `arb_excl_not_derivable` (B's `bd_arbcell` in `boxS`, requests at 100/105 ps: a behaviour with both grants high at a tick). Inside B's window it holds: `arb_excl_of_window` (QUIET or COMMIT-without-overlap gives `∀ n, (g1 n && g2 n) = false`), but only for ONE arbitration with single-step requests |
| H_ARB1 / H_ARB2 / H_AMERGE_RTZ | none | — | **open** (stay hypotheses of `AMergeC`). B's held-arbiter results (`ArbHeldTimed*`, `AMergeTimed*`) are single-scenario (one handover up to a horizon), with a relational server; no whole-run step form exists |

`ContractB` (Lean) is IpowCells' `Contract` with the join request node `ReqNode` (flat
`FbCel cgate` only at arity <= 4, else B's `bd_ctree N=5`: `reqNode_len5`), the steer `SteerB`, the
mux `MuxB`; forks, amerges, links, sources and sinks unchanged.

## 2. Weaker fields, and whether C's proof still goes through

Every bridged field above is derived exactly as IpowCells states it, so C's proof is untouched:
`contract_of_contractB : ContractB .. k → IpowCells.Contract .. k`. The direct route
(`cell_of_contractB`, via `join_of_B`, `steer_of_B`, `mux_of_B`) also works and uses only the weaker
statements C needs (`Join.cel` for the request node; LutFb + FbFirst for `uj0`/`uj1`, which is all
`mux_bound` reads). Only the arbiter fields have no B-derivable whole-run form; the weaker field B
gives is "H_ARB_EXCL for every arbitration whose request edges are inside the QUIET/COMMIT
window", and C's `amerge_inv` would need it at every tick of the run, so C's proof does NOT go
through with it without a multi-token arbiter theorem (each arbitration's request gap would have
to be shown inside the window, which is the board's open 8% overlap question).

## 3. A finding about `FbCel`

`fbCel_iff_si`: IpowCells' `FbCel F p o` is EQUIVALENT to the SI step
`o (t+1) ≠ o t → o (t+1) = F (p t) (o t)`. Its H_FB_ROUTE (`BoundedDelay lo hi o qp`), reset
agreement and H_RT_FB (`RespAfter hi p o`) are existential in `qp lo hi` and are always met by the
ideal feedback `qp = o`, `lo = hi = 0`. So `FbCel` carries no timing content beyond `FbCel.si`; the
B-side timing (C2 / tcheck Rc) is only present when `qp`, `lo`, `hi` are fixed to the routed
feedback pin and bounds. IpowCells' doc reads `FbCel` as a timing contract; that reading needs the
witnesses pinned (for example `fbCel_of_winDelay` with a given `WinDelay` wire). This is also why
the tree bridge can produce `FbCel cgate` from `Join.cel` alone (`fbCel_of_cel`). Relevant to Bfb.

## 4. The strengthened theorem and its non-vacuity

* `ipow_safe_of_contracts'`: C-8y's `ipow_circuit_safe3` (every value latched on `out0` is
  `ipowSpec b e`, and the closed values list) under `∀ o, ContractB ch (srcV b e) (extraIn o) (opAt o)`,
  H_BUNDLE, H_START_ONCE, `e < 2^32`. H_CTREE_ATOMIC, H_SEL_PIN (steers and muxes) and the mux's
  H_DELAY_LUMPED are gone; in their place are H_CTREE_LOOP + B's tree model, H_SETUP_PIN /
  H_HOLD_PIN + B's select model, H_PIN_FIFO + H_PULSE_WIDTH.
* `ipow_contractsB_satisfiable`: one run (b = 3, e = 7, IpowCells' all-quiet run with bus values
  `dvW`) meets all 83 `ContractB`s, H_BUNDLE and H_START_ONCE. Op 20 goes through B's tree model:
  `ctreeB_quiet` (for each horizon N, B's run whose leaves first switch at N + 1, every delay
  1 ps, `E = 1`, H_CTREE_LOOP true). Arity bound `ipow_jar` (every join real arity <= 5) by kernel
  `decide`.
* `ctreeB_switching`: `CTreeB` is met by a switching tree (B's run, leaves at `10 k`, the root
  really changes), so the tree bridge is not only met by quiet runs.
* As for IpowCells: the ipow-level witness is all-quiet (liveness open); it shows the B-model
  hypotheses are jointly satisfiable with the rest, not that a token run meeting them exists.

## 5. gcd_hw

* C's gcd capstone uses the same `CapNet.Cell` / `K n`, and `cell_of_contractB` and
  `contract_of_contractB` are generic in `n`: the join, steer and mux bridges apply to gcd's
  network unchanged (its `muxn` and the amerge3 cascade keep C's model / the arbiter fields).
* H_CTREE_ATOMIC in gcd sits in the FORK acknowledge trees (2 forks N=5 = `sh5`, 1 fork N=6 =
  `sh6`; its joins stop at N=4). `fbCel_of_ctreeB` is shape-generic and `leaves6_in` gives sh6's
  leaves, so `ForkC.ack` (an `FbCel cgate`) follows from `CTreeB` there too (not packaged as a
  gcd contract here).
* B's port contracts (`Contracts*.lean`) already take the steer's select timing from B's
  `SteerGates` (S_S_SETUP / S_S_HOLD, `ContractsTruncSteer.steer_pinN`): H_SEL_PIN is not a
  bare hypothesis on that route, so nothing to bridge.
* `GcdCells`' `bd_delay_gated` (29 instances) is the GATED line: not covered (see §1). The 8
  gcd arbiters: same status as ipow's (counter-run, window-only).

## 6. Results (namespace `Formal.Cells.ContractBridge`)

| theorem | statement |
|---|---|
| `root_phase`, `root_edge_leaves` | under B's tree model + H_CTREE_LOOP + lo >= 1, every root output is a phase trace and changes at τ only to the value every leaf had at τ - 1 |
| `ctreeB_cel`, `fbCel_of_ctreeB`, `reqNode_len5` | the tree request node meets `Join.cel` and `FbCel cgate`; at arity 5 `ReqNode` is the tree |
| `fbCel_iff_si`, `fbCel_of_cel`, `celL_of_all` | `FbCel` = SI step |
| `selPin_ok`, `steer_lut_of_pins`, `steer_of_B`, `sel_dec_of_held` | H_SEL_PIN from `steer_tokens`; H_SEL_DEC from H_BUNDLE |
| `uj0_of_pin`, `uj1_of_pin`, `mux_of_B` | mux select pins |
| `lumped_of_fifo`, `lumped_needs_fifo` | ungated H_DELAY_LUMPED from FIFO + width; non-monotone counter-run |
| `arb_excl_not_derivable`, `arb_excl_of_window` | arbiter exclusion: counter-run; window-only form |
| `joinC_of_joinB`, `steerC_of_steerB`, `muxC_of_muxB`, `contract_of_contractB` | the fields as IpowCells states them |
| `cell_of_contractB`, `ipow_safe_of_contracts'`, `ipow_contractsB_satisfiable`, `ctreeB_quiet`, `ctreeB_switching` | the strengthened ipow theorem and its non-vacuity |

`#print axioms` (scratch, removed): every headline theorem depends on propext, Classical.choice,
Quot.sound at most (`steer_lut_of_pins`: propext, Quot.sound; `leaves6_in`: propext).

## 7. What it does not show

* The arbiter fields on multi-token runs, and the gated H_DELAY_LUMPED (§1).
* H_RUN / H_ACK / H_PULSE_WIDTH / SelPin's windows on any routed ipow_ps: they are B-model
  hypotheses about the run (H_ACK and H_PULSE_WIDTH are protocol-wait facts of the same kind as
  IpowCells' H_RT_FB; C's network proof establishes the protocol, but not these timed forms).
* The uor's two pins on different read maps (H_OR_SAME_PATH is a simplification), and the
  select driver's own timing (`S0`/`S1` free, as in LibGapSteer).
* `CTreeB` uses the sufficient half of B's exact tree theorem; necessity (`tree_needs`) is B's, in
  B's model, and is not restated on C's traces.
