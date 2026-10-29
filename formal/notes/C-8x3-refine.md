# C-8x3: physical gcd_hw capstone without H_SEND/H_RECV; amergeB_held; the composing lemma

Shard C, probe 8x3, 2026-10-29. About 2.5 h. Follows C-8x2 (`notes/C-8x2-refine.md`) and C-8x
(`notes/C-8x-refine.md`).

STATUS: DONE for (a), (b), (c). The six new Lean files pass `./check.sh` (log at the end). No
existing file was edited.

## Verdict

- **(a) H_SEND and H_RECV are gone.** `gcd_hw_circuit_safe_phys4`: every out0 latch is
  `Nat.gcd a b` under three hypotheses only: H_CELLS_B (relaxed gate models on the observed run),
  H_START_ONCE, and a tcheck certificate (`BCert`) on 26 root channels. The four-phase protocol
  and the bundling `Held` of all 465 channels are now CONCLUSIONS (`gcd_hw_joint`,
  `gcd_hw_send_recv`). One induction over time derives both: the protocol at step t uses `Held`
  only before t, and `Held` at t uses the protocol only up to t.
- **(b) `amergeB_held` proved.** On the relaxed model an arbiter stage's output is bundled when
  its two inputs are. Two new kernel-checked facts about 8j's reachable set support it: the input
  named by the index bit is busy whenever the output is, and the index bit does not move inside an
  output transaction. 5 of the 9 arbiter stages become structural (chan 463, plus 457, 460, 462
  and 464). The other 4 (456, 458, 459, 461) lie on cycles that contain no mux, so they stay
  roots. Roots: 31 → 26. Every root has an existing A row (8w): **no new tcheck row is needed for
  any root**. Chan 463 no longer needs a row.
- **(c) The composing lemma is proved, at cell level.** `field_of_sampled` composes C-8x's
  `sampled_eq_zd` (tcheck row + H_TXWIN), H_FN (the netlist's zero-delay function is the cell
  function) and H_LAUNCH (the launch values are the input buses right after the output's offer)
  into the relaxed data field. Instances: `joinB_of_phys`, `forkB_of_phys` and `steerB_of_phys`
  take a cell's handshake half and derive the full relaxed cell. Joint witness for the join
  (`wjoin_hyps`). The derived field holds on a run where the OLD all-time field fails
  (`wjoin_old_fails`). NOT plugged into phys4 (see "Not covered").

## Files

| file | what |
|---|---|
| `formal/lean/Formal/Net/OpsBusy2.lean` | `HeldStep`, `HeldTo`; `steer_invT`, `mux_invT`, `muxn_invT` (8f/8j invariants, `Held` only before t) and `*_protoT`; `OpProtoT` (+ `toOpProto`); `fork_opT join_opT link_opT amerge_opT src_opT sink_opT steer_opT mux_opT muxn_opT`; `cell_protoT` (old cells), `protoT_of_mod`, **`cell_protoT_B`** (relaxed cells) |
| `formal/lean/Formal/Net/OpsBusy2Held.lean` | **`net_joint`** (any network); `forkB_heldT joinB_heldT steerB_heldT link_stepT linkB_heldT`; `amerge_busy`, `amerge_won_stable` (kernel `decide` over `atbl`), **`amergeB_heldT`**, **`amergeB_held`**; `StructK2`; **`cellB_heldT`** |
| `formal/lean/Formal/Net/CapstoneRefine3Cert.lean` | `idle_untilT`, `busy_coverT`, `heldStep_of_txwin`, **`heldStep_of_bcert`** |
| `formal/lean/Formal/Net/CapstoneRefine3.lean` | `rootIds3` (26), `rankL3`, `struct3_all`/`struct3_chk` (kernel `decide`), **`gcd_hw_joint`**, **`gcd_hw_circuit_safe_phys4`**, `gcd_hw_send_recv`, `roots3_sub`, `phys4_hyps_of_phys3`, `gcd_hw_phys4_witness`, `strict_phys4_hyps` |
| `formal/lean/Formal/Net/CapstoneRefine3Fn.lean` | **`field_of_sampled`**, `held_const`, `JoinH`/`ForkH`/`SteerH` (handshake halves), `BranchPhys`, **`joinB_of_phys`**, **`forkB_of_phys`**, **`steerB_of_phys`** |
| `formal/lean/Formal/Net/CapstoneRefine3FnWit.lean` | `wQ`, `wI`, `wXQ` (H_TXWIN), `wQ_proto`, `wI_proto`, `wI_held`, `wjoin_H`, **`wjoin_hyps`**, `wjoin_field`, **`wjoin_old_fails`**, `wQ_bcert` |
| `formal/lean/Wip/C8x3/probe_amerge.py` | which arbiter stages can be structural (cycle test), roots and rank table; writes `probe_out.txt`, `roots3.tsv` |
| `formal/lean/Wip/C8x3/tables3.lean.txt`, `probe_out.txt`, `roots3.tsv` | its output (the Lean tables, the 26 roots with 8w's expectation, the 5 new structural stages with their rank) |
| `formal/lean/Wip/C8x3/amerge_check.py` | Python pre-check of the two `atbl` facts before the kernel `decide` |
| `formal/lean/Wip/C8x3/axioms.lean` | `#print axioms` of the headline theorems |

## The Lean, in plain words

### (a) The time-bounded protocol

**Why the old proof was circular.**
- 8f's `OpProto` gives the protocol at step t if the operator's inputs
  are `Held` at ALL times.
- `net_protocol` therefore needs `Held` everywhere first.
- C-8x2's `held_struct` derives `Held` from the protocol everywhere.
- So phys3 had to assume one of the two (H_SEND/H_RECV).

**What the proofs actually use.**
- The steer, mux and muxn invariants (`steer_inv`, `mux_inv`, `muxn_inv`) are inductions from 0
  to t. They read `Held` of the select only on steps s < t.
- The other kinds (fork, join, link, arbiter, source, sink) never read `Held` in their protocol
  proof.
- `cell_protoT_B` re-proves the protocol spec under the weaker premise: inputs `HeldTo t`
  (`Held` on every step s < t).

**Structural `Held` at one step.**
- `cellB_heldT`: an output's `Held` at step t follows from the protocol on steps ≤ t and the
  inputs' `Held` on steps ≤ t.
- The steer needs its select on steps ≤ t; fork, join, link and arbiter need their inputs at t.
- These are C-8x2's `*B_held`, with every all-time premise cut back to what the proof reads.

**Root `Held` at one step.**
- `heldStep_of_bcert`: a tcheck certificate gives `Held` at step t from the receiver rule on
  steps ≤ t.
- C-8x's `busy_cover`/`idle_until` only look backwards in time.

**`net_joint`.** This works on any network. It is a strong induction on t, proving at each t:
1. the protocol rules at t for every channel, from `OpProtoT` (needs `Held` before t, by
   induction);
2. `Held` at step t for every channel, from a supplied rule. For gcd_hw the rule is an inner
   induction on `rankL3`:
   - structural producers use `cellB_heldT`; their inputs have a smaller rank, and steps < t come
     from the outer induction;
   - the 26 roots use `heldStep_of_bcert`.

**`gcd_hw_circuit_safe_phys4`.** It feeds `gcd_hw_joint`'s `Held` into C-8x2's
`gcd_hw_circuit_safe3B`. Its two conclusions are the same as phys2/phys3 and 8s's
`gcd_hw_circuit_safe3`:
- every out0 close carries `Nat.gcd a b`;
- the closed-value list is `replicate #closes (gcd a b)`.

### (b) The arbiter stage

`AMergeB x y z g1 g2` (relaxed): `z.dat = 2·(won ? y.dat : x.dat) + won` while z is busy, where
`won = g2 ∨ A2` (A2 = y.ack).

Two facts, checked by kernel `decide`:
- **`amerge_busy`**: in each of the 38 reachable states of 8j's `atbl` where z is busy, the input
  named by `won` is busy.
- **`amerge_won_stable`**: for every reachable state and every successor the gate model and the
  protocol allow, if z is busy before and after the step, `won` does not change.
  - Reason: while z.ack is high no grant can rise (H_ARB), so A2 cannot rise.
  - At z's offer both acks are low (H_AMERGE_RTZ), so `won` is the grant.

`amergeB_heldT` combines these with the protocol up to t: z's bus moves only if the selected
input's bus moves, and that input is `Held`. `amergeB_held` is the all-time corollary.

**Graph data** (`probe_amerge.py`):
- With `amerge` counted as structural, adding each arbiter stage to the structural set either
  keeps the dependency graph acyclic or not:
  - acyclic for 457, 460, 462, 463, 464;
  - cyclic for 456, 458, 459 and 461 (461's cycle runs through 454). These loops pass through
    fork/steer/link/join and an arbiter stage, but no mux.
- So the roots are the 21 two-input muxes, the 3-input mux (out0, chan 416) and those 4 stages:
  26 in all.
- `struct3_chk` re-checks the rank table in the kernel.
- All 26 roots have an A row on 8w's expectation list (`roots3.tsv`).

### (c) The composing lemma

`field_of_sampled` (generic). Let P be the output's observed channel, with C-8x's TxWin and
separation (i.e. a tcheck DAG or cert row), reset and the receiver rule. Hypotheses:
- **H_FN**: `zdBus runs data k = fn (vin k)`.
- **H_LAUNCH**: `vin k = IN (r+1)` at the k-th offer r.
- **H_STABLE**: `IN` is constant over each output transaction.

Then `P.dat t = fn (IN t)` at every busy instant. Proof: `busy_cover` finds the transaction, then
`sampled_eq_zd`, H_FN, H_LAUNCH and H_STABLE are rewritten in turn.

For join, fork and steer, H_STABLE is DERIVED, not assumed:
- the inputs are busy whenever the output is (8w's `JInv`/`FInv`/`SInv`, from the handshake half
  and the protocol);
- the inputs are `Held`;
- so their buses are constant across the output's transaction (`held_const`).

`joinB_of_phys` / `forkB_of_phys` / `steerB_of_phys` turn the handshake half
(`JoinH`/`ForkH`/`SteerH`), the protocol, the inputs' `Held`, the output's tcheck data, H_FN and
H_LAUNCH into the full relaxed cell.

**Witness** (`CapstoneRefine3FnWit`):
- Output `wQ`:
  - C-8x's witness runs `wrun` (tcheck DAG row `wcheck`);
  - req on 6..10 and ack on 8..12 of a 20-tick period. C-8x's `wP` cannot be a join's output:
    its req falls 2 ticks after ack rises, faster than any join allows.
- Input `wI`: req on 5..9, ack on 9..13, bus = the token bit of the period.
- `wjoin_hyps`: all hypotheses of `joinB_of_phys` hold.
- `wjoin_field`: the derived relaxed field holds.
- `wjoin_old_fails`: the all-time join field fails at t = 20. The output is idle there and still
  shows the previous run's settled 0, while the input already carries 1.

## Hypotheses and non-vacuity

| name | where | content | non-vacuity |
|---|---|---|---|
| H_CELLS_B | phys4 | relaxed gate models on the observed run (C-8x2) | 8t's run, `gcd_hw_phys4_witness`; also C-8x2's `chS` where the OLD models fail (`strict_phys4_hyps`) |
| H_START_ONCE | phys4 | `start` offered at most once (8s) | 8t (`w_start_once`) |
| H_TCHECK_ROOT | phys4 | `BCert` on the 26 roots (`rootIds3`) | 8t with `exempt` (as in 8x/8x2); the `dag` constructor: 8x's `refine_witness` (one channel), and here `wQ_bcert` |
| `Disj` | per operator | no self-loop | checked (8x2's `disj_ok`) |
| (c) H_FN, H_LAUNCH, tcheck row/H_TXWIN, handshake half, protocol, inputs `Held` | `joinB_of_phys` (fork/steer analogous) | see above | `wjoin_hyps` (join). No witness built for `forkB_of_phys` / `steerB_of_phys` separately |

phys4's hypotheses follow from phys3's (`phys4_hyps_of_phys3`, `roots3_sub`): it drops H_SEND,
H_RECV and 5 root certificates.

## Not covered

- **(c) is not in the capstone.** phys4 still assumes the relaxed data fields (H_CELLS_B). To
  derive them inside the capstone, the data field at step t would have to go inside the joint
  induction:
  - the derivation needs the protocol and the inputs' `Held`, which come from H_CELLS_B;
  - the field at t and t+1 needs the receiver rule only up to t and the inputs' `Held` up to t,
    so it looks feasible.
  - A per-channel choice would also be needed:
    - a sampled channel would take a tcheck row + H_FN + H_LAUNCH;
    - a ghost channel would keep its field by construction.
  Not done.
- H_FN (per cell type, a functional check against the obligation netlist) and H_LAUNCH (launch
  values = input buses at the offer: C-8x's R3/R4) are open. They are stated precisely here and
  witnessed on a toy netlist only.
- No composing lemma yet for the link (latch-D, 175 channels), the mux/muxn or the arbiter data
  fields.
- The 4 arbiter stages on mux-free cycles still need certificates (A rows exist on 8w's list).
  The muxn select (chan 415) still has no E row for its relaxed field (C-8x2); that is a
  H_CELLS_B question, not a root certificate.
- Liveness and timing are not covered. The root certificates in every gcd witness are `exempt`.

## Fidelity

| model | grade | why |
|---|---|---|
| `OpProtoT`, `net_joint` | A (proved) | strictly weaker premises than 8f's `OpProto`/`net_protocol` (`toOpProto`) |
| `amergeB_held` | A (proved) | from the relaxed arbiter model; 8j's `atbl` reachable set, re-checked |
| phys4 hypotheses | B | H_CELLS_B is the relaxed gate model (C-8x2); roots need real tcheck rows on the routed design, which no witness here exercises |
| (c) H_FN, H_LAUNCH | C | stated, open; toy witness only |

## Check log (2026-10-29)

    cd /home/user/asyncfpga3/formal
    ./check.sh Formal/Net/OpsBusy2.lean Formal/Net/OpsBusy2Held.lean \
      Formal/Net/CapstoneRefine3Cert.lean Formal/Net/CapstoneRefine3.lean \
      Formal/Net/CapstoneRefine3Fn.lean Formal/Net/CapstoneRefine3FnWit.lean
    [check] textual scan
    [check] lean Formal/Net/OpsBusy2.lean
    [check] lean Formal/Net/OpsBusy2Held.lean
    [check] lean Formal/Net/CapstoneRefine3Cert.lean
    [check] lean Formal/Net/CapstoneRefine3.lean
    [check] lean Formal/Net/CapstoneRefine3Fn.lean
    [check] lean Formal/Net/CapstoneRefine3FnWit.lean
    [check] axiom audit
    [audit] 4447 declarations checked
    [check] OK

`Wip/C8x3/axioms.lean`: `gcd_hw_circuit_safe_phys4`, `gcd_hw_joint`, the witnesses and
`joinB_of_phys` depend on {propext, Classical.choice, Quot.sound}; `amergeB_held` on {propext,
Quot.sound}. No sorry, no native_decide. The table checks (`struct3_all`, `roots3_sub_all`,
`amerge_busy`, `amerge_won_stable`) are kernel `decide +kernel`.

Reproduce the data: `python3 lean/Wip/C8x3/probe_amerge.py` (roots, rank table; reads 8x2's
`classify.py` front half and `CapstoneNet.lean`), `python3 lean/Wip/C8x3/amerge_check.py`.
Oleans needed before `check.sh` (targeted builds, Mathlib-free):
`./slot.sh lake build Formal.Net.CapstoneRefine2Strict Formal.Net.CapstoneRefineWit`.
`CapstoneRefine3.lean` takes about 40 s (the kernel `decide`s); the rest a few seconds each.
