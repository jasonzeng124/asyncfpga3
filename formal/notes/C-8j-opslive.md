# C-8j: finishing operator composition (track 8, Phase 3)

## Verdict

**Works for (1) and (2-cell); (3) and (4) reframed and left open with
measured effort.** Core Lean, no Mathlib, no `sorry`/`axiom`/`native_decide`;
`check.sh` passes (1199 declarations, chain listed below). About 3 h.

1. **gcd_circuit non-vacuity: done, and it shows the 8b graph is live ONLY at
   `a = 0`.**
   - `gcd_witness`: for every `b`, an explicit run satisfying every hypothesis
     of `gcd_circuit` with `a = 0` in which `out` latches a token at t = 23
     whose value is `Nat.gcd 0 b`.
   - `gcd_stuck` / `gcd_no_token` (new, negative): for EVERY `a ≠ 0` (entry
     condition `a`, `b` odd) and every run satisfying the hypotheses, `out.req`
     never rises, so no result is ever latched. `gcd_circuit` is true for
     `a ≠ 0` only because the circuit deadlocks.
   - Cause (`gcd_loop_stuck`): 8b's hand-drawn graph has no storage on its data
     loop, so the acknowledge cycle
     `hA.ack ← hA2.ack (fork C) ← jA.ack (join wire) ← aT.ack ∨ aF.ack (steer OR)
      ← a1.ack (fork C) ← backA.ack (sub wire) ← hA.ack (bd_mux y_ack = C(j1, z_ack))`
     can never fire once the first token is steered into the loop. This is 9's
     storage rule from the safety side.
2. **control_merge / merge (`bdc_amerge2`): cell spec done, winner forced at
   the cell; network-level forcing open.**
   - `AMerge` (gate model, grants FREE), `amerge_closed` (38-state reachable
     set, kernel `decide`), `amerge_proto`, `amerge_op`: `OpProto` + `OpData`
     with the token equation relative to the winner stream `ω = winner (ch z)`
     (read off the circuit). `Ops.net_refines`/`net_determinate` apply as is:
     determinate modulo `ω`.
   - `amerge_forced`: under H_EXCL_REQ (the two requests never high together),
     the winner of each token is the input requesting at its offer: the
     arbiter's free choice is never exercised.
   - Cell obligation to B: `H_ARB_EXCL` (never both grants) = B's
     `ArbBinary.settled_exclusion` + `exclusion_transport` / `rt1_exclusion`
     (B-obligations R1, R2, A2). `H_ARB` (grant follows its request, rises only
     with the other grant and A0 low) = B's `stA_eq` (q frozen while A0 high),
     `gr1_eq`, `gr2_eq` at settled level.
   - **New obligation H_AMERGE_RTZ** (found here): bdc's index `won = g2 | A2`
     with `A2 = C(g2, A0)`; in an SI model the next winner's grant and `z_req`
     can overtake `A2↓`, and the next token is offered with a stale index =
     the wrong input's data (`amerge_reach.py` without the rule: counters
     diverge). In the fabric it is the race `A0↓ → ua2 → A2↓` (one C LUT)
     against `A0↓ → ustate → ugrant → uor → udly → z_req` (the whole matched
     delay), so it should hold with a wide margin, but it is a timing fact and
     belongs in track 10's checker next to B's H_MUX_RTZ.
   - NOT done: network-level forcing (that under H_ONE_INVOCATION the circuit's
     winner stream equals a stream computed from the token semantics, e.g.
     `ω 0 = 0`, `ω (k+1) = route of token k`). What is missing is a ring
     counting argument (z → fork → ... → cond_br → back edge) showing that at
     each z offer exactly one input is pending and which one; with that,
     `amerge_forced` turns `amerge_op`'s oracle into a fixed stream and the
     network is determinate. 8b proved the token-level analogue
     (`KahnGcdCM.G2_wfOn`). Estimate 0.5-1 day.
3. **3-way mux: bdc does NOT build it as a tree of 2-way muxes.** `emit_muxn`
   is a one-level N-way generalisation of bd_mux
   (`j_k = C(in_k_req, ctl_req·(s==k))`, `z_req = δ(OR j)`,
   `in_k_ack = C(j_k, z_ack)`, `ctl_ack = z_ack`), and its header says why: a
   tree needs the index at every level, a forked index waits for the branch
   the index did not select, and deadlocks. (A tree with a STEERED index would
   be correct at token level, but it is not what bdc emits.) So I modelled
   bdc_muxn N = 3 in the 8f SI model: `muxn_reach.py` finds 594 reachable
   states, 0 protocol violations (the same script gives 8f's 132 at N = 2, a
   cross-check). The Lean closure (8f's OpsMux method on 594 states) is not
   written: ~0.5 day, and the kernel `decide` must be split per state or per
   input to stay under the memory limit (8f's 132-state check took 20 s).
4. **Liveness: negative result only.** The 8b graph is NOT live for `a ≠ 0`
   (item 1). A liveness theorem needs a graph that has storage on each cycle
   (bdc puts `bd_link`s in front of matched-delay cells; 9a/9b's 3-stage /
   one-token rule), i.e. a link operator in the Ops framework (8f open item 3)
   and the graph bdc actually emits for gcd_hw (13 control_merges, 3-way mux).
   No bound obtained. Estimate: link op cell 0.5 day, network liveness under
   fairness 1-2 days (8a has it for pipelines, 9a for rings).

## Files

- `formal/lean/Formal/Net/OpsWitness.lean`: `GcdHyps` (every hypothesis of
  `gcd_circuit`, bundled), `gcd_circuit_hyps`, the run (`St`, `tbl`, `fin`,
  `S`, `wch`, `dv`), the per-cell lemmas `w_mux`, `w_fork2`, `w_fork4`,
  `w_join1`, `w_join2`, `w_steer`, `w_sink`, `w_src`, `w_ibuf`, `w_env_out`,
  `w_held`, and `gcd_witness`, `gcd_witness_value`.
- `formal/lean/Formal/Net/OpsLive.lean`: `hyps_ops`, `gcd_loop_stuck`,
  `gcd_stuck`, `gcd_no_token`.
- `formal/lean/Formal/Net/OpsCM.lean`: `AS`, `atbl`, `AConcl`,
  `amerge_closed`, `amerge_guar`, `AMerge`, `amerge_inv`, `amerge_proto`,
  `winner`, `winner_at`, `amergeEq`, `amerge_op`, `amerge_forced`.
- `formal/lean/Wip/C8j/gcd_run.py`: unit-delay simulator of the gcd network;
  `-lean` prints the table. Also shows: 1-place initial-token buffers deadlock
  even at `a = 0`; `a ≠ 0` deadlocks with either capacity.
- `formal/lean/Wip/C8j/amerge_reach.py`: reachable set of `AMerge`
  (`-lean` prints `atbl`); remove the H_AMERGE_RTZ line to see the stale-index
  divergence.
- `formal/lean/Wip/C8j/muxn_reach.py N`: reachable set of bdc_muxn (N = 2: 132,
  N = 3: 594).
- `formal/lean/Wip/C8j/Axioms.lean`: `#print axioms` (proves nothing). All main
  theorems: only `propext`, `Classical.choice`, `Quot.sound` (the closure
  `amerge_closed` none). `Classical.choice` enters through `winner`
  (classical decidability of "the k-th offer's index bit is 1") and core `simp`.
- `tbl.lean`, `atbl.lean` in `Wip/C8j/`: generated tables (inputs, not proofs).

## Run

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    export LEAN_PATH=$PWD/.lake/build/lib/lean
    # needs 8f's oleans (Ops, OpsFork, OpsJoin, OpsSteer, OpsMux, OpsGcd) and KahnGcd
    for f in OpsWitness OpsLive OpsCM; do
      ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/$f.olean Formal/Net/$f.lean; done
    ../slot.sh lean Wip/C8j/Axioms.lean
    cd .. && ./check.sh Formal/Net/Prelim.lean Formal/Net/Handshake.lean Formal/Net/KahnLTS.lean \
      Formal/Net/Kahn.lean Formal/Net/KahnGcd.lean Formal/Net/Ops.lean Formal/Net/OpsFork.lean \
      Formal/Net/OpsJoin.lean Formal/Net/OpsSteer.lean Formal/Net/OpsMux.lean Formal/Net/OpsGcd.lean \
      Formal/Net/OpsWitness.lean Formal/Net/OpsLive.lean Formal/Net/OpsCM.lean
    # -> [audit] 1199 declarations checked, [check] OK

Times (unloaded): OpsWitness 3 s, OpsLive 3 s, OpsCM 5 s. The lead must add
the three modules to `Formal.lean` (I don't own it).

## How the witness is checked

The run is a table of 32 rows (bitmasks of 25 request wires, 25 acknowledge
wires, 4 mux C-elements), from t = 31 on constant (`fin`). `chk P tbl fin`
checks a Boolean step property `P s s'` on every consecutive pair and on
`(fin, fin)`; `chk_all` turns it into `∀ t`. Every gate rule of every cell
instance is one such check (`by decide`, kernel evaluation of a 32-row list,
no 2^n case split; the whole file checks in seconds). The data is symbolic in
`b`: every bus is constant in time (`a = 0`, every select is 0), so `Held` is
`rfl` and the data equations are definitional. The environment in the run:
- sources: one token each (offer, wait ack, release, stay idle);
- out consumer: `ack` copies `req` one tick later;
- initial-token buffers: **2-place** FIFOs holding the initial 0. A 1-place
  buffer deadlocks (gcd_run.py): the mux acknowledges its select token only
  after `hA` is acknowledged, which needs `cnd` acknowledged, which needs the
  buffer to accept the next select token while its own output is still open.
  So H_INITBUF of 8f is satisfiable but only by a buffer of capacity ≥ 2 (or a
  link pair); this is an observation from simulation, not a theorem.

## Fidelity of the models used

- Witness run: every gate moves to its function of the previous tick (delay
  exactly 1 tick), a legal instance of 8f's SI/DI models (unbounded inertial
  delay). It shows satisfiability of the hypotheses, nothing about real delays.
- `AMerge` (new): SI, binary. The arbiter is abstracted to its handover
  behaviour (H_ARB, H_ARB_EXCL): metastability, runts and the tie are B's
  business (the free grants cover any resolution order). C-elements A1/A2
  H_CEL_SI; OR + matched delay lumped (H_DELAY_LUMPED); data path ideal
  (H_DATA_COMB: `z.dat = 2·(won ? y : x) + won` at every tick, the real data
  delay goes into `Held z`). H_AMERGE_RTZ is a route timing obligation (above).
  The cascade for n ≥ 3 inputs is not modelled.
- Everything else is 8f's (see C-8f-ops.md).

## Timing obligations added (for track 10)

| id | where | statement |
|---|---|---|
| H_AMERGE_RTZ(m) | bdc_amerge m | after `A0↓`, the previous winner's `A_k` (C-element) falls before `z_req` rises again: min(A0↓ → ustate → ugrant → uor → udly → z_req at consumers) > max(A0↓ → ua_k → A_k → won → z_data at consumers) |
| H_ARB_EXCL(m) | bd_arbiter | never g1 = g2 = 1 (B: R1, R2, A2) |
| H_EXCL_REQ(m) | control_merge at a loop header | entry and back-edge requests never pending together: follows from H_ONE_INVOCATION at token level (8b), the circuit-level derivation is open (item 2) |

## What it buys the project

- `gcd_circuit` is now known to be non-vacuous, and also known to be the wrong
  target: on 8b's graph it is true for `a ≠ 0` only by deadlock. Any
  end-to-end gcd claim has to be made on a graph with storage on its cycles
  (bdc's real output), and has to come with a liveness theorem. Non-vacuity
  checks of this kind (an explicit run that delivers) should accompany every
  safety theorem of this shape.
- The control_merge cell is now in the composition framework, with its
  nondeterminism isolated in one oracle stream and a cell-level condition
  (H_EXCL_REQ) under which the oracle is forced. One new timing obligation
  (H_AMERGE_RTZ) for the checker.
- bdc_muxn's design rationale (no tree) is confirmed and its SI model is
  protocol-safe at N = 3 by explicit search (594 states).
