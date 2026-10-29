# C-8x: physical (bounded-delay) traces → zero-delay Ops traces (capstone H_BUNDLE)

Shard C, probe 8x (second attempt), 2026-10-29. About 3 h.
The first 8x died. Its leftovers are `Wip/C8x/Axioms.lean` and `Wip/C8x/RankGen.lean`. They
refer to `Formal/Net/CapstonePhysSafe.lean` and `CapstonePhysRefine.lean`, which are not on
disk, so nothing of that attempt was reusable except the idea of a combinational rank.
That idea is not used here.

STATUS: per-channel refinement DONE (proved, witness, necessity). Network lift DONE as a
conditional theorem; the refinement of H_CELLS (H_ZD_AGREE) and H_DERIVED remain open.
All four claimed files pass `./check.sh` (log at the end).

## Verdict

**Per channel: proved.** For a bundled-data channel whose physical traces satisfy 10a's
per-arc `BoundedDelay` run semantics and one of tcheck's verdicts (DAG `checkArr`, or the
four conjuncts of the cert `cverdict`), and which is windowed into single-launch runs (H_TXWIN),
two things hold:
- every bus value the capture latch can sample inside a transaction is the **zero-delay value**
  of that transaction's obligation netlist;
- the observed channel satisfies the Ops `Held` (H_BUNDLE).

The new mathematical step is **R2** (`run_settles`). In every bounded-delay run, glitches
included, a node that is quiet from `t` on already holds its zero-delay value at `t`. tcheck's
separation therefore gives the VALUE at the request, not only the ORDER.

**Network: proved conditionally.** `gcd_hw_circuit_safe_phys` replaces the capstone's
H_BUNDLE with per-channel tcheck certificates plus three named hypotheses: H_ZD_AGREE, H_RECV,
and H_DERIVED for the channels no row covers. The physical → zero-delay refinement of
**H_CELLS** (R2 at the network level, R3 and R4) is NOT proved. It is stated precisely below.

## Files

| file | what |
|---|---|
| `formal/lean/Formal/Net/CapstoneRefine.lean` | `zdEval`, **`run_settles`**, **`settled_of_quiet`**, `settled_of_win`, **`dag_settled`**, **`cert_settled`**, `bv`, `TxWin` (H_TXWIN), `zdBus`, `off_in_win`, **`sampled_eq_zd`**, `capture_window`, `idle_until`, `busy_cover`, **`held_of_txwin`**, `zd_token`, `zd_close`, `sep_dag`/`sep_cert`, **`sampled_eq_zd_dag`**, **`held_dag`**, **`sampled_eq_zd_cert`**, **`held_cert`** |
| `formal/lean/Formal/Net/CapstoneRefineWit.lean` | non-vacuity `refine_witness`; necessity `stale_without_check` |
| `formal/lean/Formal/Net/CapstoneRefineNet.lean` | `BCert`, `held_of_bcert`, `obsCh`, `held_of_agree`, **`held_net`** (any network) |
| `formal/lean/Formal/Net/CapstoneRefineGcd.lean` | `gcd_hw_init`, **`gcd_hw_circuit_safe_phys`**, `gcd_hw_phys_witness` (needs CapstoneWalk + CapstoneWitness3 oleans) |
| `formal/lean/Wip/C8x/Axioms.lean`, `RankGen.lean` | the dead first 8x (refer to missing files; do not compile) |

## The Lean (statements in plain words)

### R2: settling to the zero-delay value

- **`zdEval net g b v`.** The netlist evaluated with every delay set to zero, launch node at `b`,
  the run's own node functions `g`.
- **`run_settles`.** Assumes `net.WF` and `Run net sig`. Every node equals
  `zdEval net r.g (sig 0 1) v` from time `1 + v·hmax` on, and keeps that value.
  - The proof is strong induction on the node index. `BoundedDelay.settle` makes each pin copy
    its settled source.
  - H_LOCAL and H_ZERO_DELAY_FN make the node a function of those pins.
- **`settled_of_quiet`.** A node with no change at or after `t` equals its zero-delay value at
  `t`.
  - Nothing is assumed about glitches. Pure delay, pulses pass, the delay can vary per event.
    Once the node is quiet, its value is the zero-delay one.
  - So **no monotone-routing / no-glitch hypothesis is needed** for this step. Those
    hypotheses matter only for tcheck's credited rules (H_CLEAN_EDGE in `xverdict`, 10l),
    which this file does not instantiate.
- **`dag_settled`.** Assumes `checkArr net req data setup = true`. Once the request node
  changes at `v`, every data node holds its zero-delay value from `v + 1 - setup` on.
  - The proof is `checkArr_sound` plus `settled_of_quiet`.
- **`cert_settled`.** The same from the cert conjuncts. `potOK_sound` bounds the request
  change of the late-side run from below; `changes_in_winArr` bounds the data changes of the
  data-side run from above.

### Per channel, many transactions

**`TxWin P sig data R` (H_TXWIN).** The physical channel `P` has req/ack at the capture cell's
pins; `P.dat` is the capture-pin bus as `bv data.length` of its bits. The fields:
- `τ k`: the launch of transaction `k`;
- `idle`, `count`: the channel is idle at `τ k` with exactly `k` offers made
  (H_LAUNCH_AFTER_CLOSE, as in 8w's `TxCover`);
- `reqIn`: offer `k` is a request change of run `k` (H_REQ_IN_RUN);
- `win`: on `[τ k, τ (k+1))` the bus is bit for bit run `k`'s data nodes, shifted by `τ k`
  (H_DATA_IS_RUN).

`win` is stronger than 8w's `datIn`, which only attributed bus changes to runs. The stronger
form is what lets the VALUE through.

The theorems:
- **`sampled_eq_zd`.** Assumes per-run separation (data changes ≤ request change). Then at
  every instant `t` after offer `r` with the channel busy on `(r, t]`, `P.dat t = zdBus runs
  data k`, the zero-delay bus of run `k`.
  - Proof: the offer lies in `[τ k, τ (k+1))` (`off_in_win`, from `count`), and `t < τ (k+1)`
    because the channel is idle at every launch. Then `win` and `settled_of_quiet` finish it.
- **`capture_window`** (H_LATCH_WINDOW). A latch closing at `tc` with setup/hold margins
  `su`/`hd` sees one constant value, the zero-delay one, on `[tc - su, tc + hd]`. The
  condition is that this window lies after the offer and inside the transaction.
- **`held_of_txwin`.** Adds `Init P` and `RecvStep P` (H_RECV) and concludes the Ops `Held P`.
  - `busy_cover`: every busy instant belongs to an offer with the channel busy since.
  - The only delicate case is an offer at `t` with the channel busy at `t`. `idle_until` rules
    it out: from a launch to the next offer, the receiver rule keeps the channel idle.
- **`zd_token`.** The token value `P.dat (r+1)` (the Ops convention) is the zero-delay bus.
- **`zd_close`.** The value at the close (`TokAt`) is the zero-delay bus, for a channel that
  obeys `Protocol`.
- `held_dag`, `sampled_eq_zd_dag` (DAG verdict) and `held_cert`, `sampled_eq_zd_cert` (cert
  verdict) are the instantiations.

### Network lift

**`BCert P`**, one per channel, has three constructors:
- `dag`: a tcheck DAG row PASS (`net.WF`, `checkArr = true`, runs, `TxWin`);
- `cert`: a tcheck cert row PASS (the four `cverdict` conjuncts, two run families, `TxWin`);
- `exempt (h : Held P)`: H_DERIVED, for channels with no row.

The theorems:
- **`held_net`** (any network `C`). Assumes per channel `BCert (obsCh ch pdat c)`, plus
  `Init`, H_RECV, and H_ZD_AGREE (`inTx (ch c) t → (ch c).dat t = pdat c t`). Concludes
  `∀ c, Held (ch c)`.
  - `obsCh ch pdat c` is the observed channel: the Ops req/ack wires and the capture-pin bus.
- **`gcd_hw_init`.** `Init` of every gcd_hw channel from H_CELLS alone, via `cell_proto`'s
  `initIn`/`initOut`, with no H_BUNDLE.
- **`gcd_hw_circuit_safe_phys`.** For `a, b < 2^31`, H_CELLS, H_START_ONCE, H_RECV,
  H_ZD_AGREE and H_TCHECK (`∀ c, BCert ..`) give the same conclusion as
  `gcd_hw_circuit_safe3`: out0 latches only `Nat.gcd a b`.

## Hypotheses (all named; non-vacuity)

| name | where | content | non-vacuity |
|---|---|---|---|
| H_BOUNDED_DELAY, H_QUIESCENT, H_LAUNCH, H_LOCAL, H_ZERO_DELAY_FN | `Run` (10a) | per-run semantics | `wrun` (witness) |
| tcheck PASS | `checkArr = true` or the cert conjuncts | the verdict row | `wcheck` by `decide` |
| H_TXWIN = H_LAUNCH_AFTER_CLOSE + H_REQ_IN_RUN + H_DATA_IS_RUN | `TxWin` | the gate/timing correspondence per transaction | `wX` (witness) |
| H_RECV | `RecvStep` | the consumer's ack moves only when it differs from req | `wRecv`; network: 8t's run, via `gcd_hw_protocol` |
| reset | `Init` | | `wInit`; network: derived (`gcd_hw_init`) |
| H_LATCH_WINDOW | hypotheses of `capture_window` | the latch's setup/hold window is inside the transaction | none given separately (it is a premise of a corollary) |
| H_ZD_AGREE | `held_net` | the Ops bus equals the capture-pin bus while the channel is busy | 8t's run with `pdat = dat` (`gcd_hw_phys_witness`) |
| H_DERIVED | `BCert.exempt` | physical `Held` for channels with no tcheck row | 8t's run (all exempt). **Joint witness exercises only `exempt`**; the `dag` constructor is exercised by `refine_witness` on one channel |
| H_START_ONCE, H_CELLS | capstone | unchanged | 8t |

**Not needed**:
- monotone / no-glitch routing (R2 tolerates glitches);
- H_CLEAN_EDGE (only for credited rules, not instantiated).

**Load-bearing**:
- `stale_without_check`: with the request faster than the data, tcheck rejects, and the
  sample right after the request is the OLD value, not the zero-delay one.
- 8w's `held_needs_close` shows the launch-ordering fields cannot be dropped.

**Witness (`refine_witness`).**
- Netlist: launch → data with delay [1,2], launch → req with [5,6]; tcheck passes.
- Channel: period 20 ps, four-phase, token `k` = `k mod 2`.
- All hypotheses of `held_dag` / `sampled_eq_zd_dag` hold; the bus is 0 in transaction 0 and 1
  in transaction 1. The conclusions are applied, not just the hypotheses checked.

## What remains (precise)

1. **H_ZD_AGREE: the refinement of H_CELLS.** The capstone needs an Ops trace `ch` that
   satisfies the cells' zero-delay equations pointwise in time (`Join.dat`, `Fork.dat`,
   `Steer.dat`, the link's H_LATCH_OPEN/HOLD) AND agrees with the capture-pin bus while each
   channel is busy. `sampled_eq_zd` proves that the capture-pin bus of channel `c` in transaction
   `k` is `zdBus`, the zero-delay value of `c`'s obligation netlist at its launch. What is
   missing:
   - **H_FN.** `zdEval` of the obligation netlist (its LUT functions) is the Ops cell's function
     `g` of its input tokens. This is a LUT-level functional check, per cell type, against the
     netlist tcheck analysed (H_NETLIST).
   - **R3 (latch).** The obligation's launch value is the upstream link's latched token, and that
     latch holds it over the window. This is rules I/H/W plus `capture_window` applied to the
     upstream link's own input channel.
   - **R4 (control).** The steer/mux LUTs read the settled select (rule E, which is again an
     instance of `dag_settled`). The arbiter's grant is consistent (J).
   - **The ordering argument across channels.** The zero-delay `ch` changes a bus only when an
     upstream latch changes, and that must not happen while a downstream channel is busy. On the
     zero-delay traces this is 8w's per-cell `*_held` plus a network closure (the cycle argument),
     still open for mux/muxn/amerge. Here it is replaced by the physical certificates, which is
     exactly why H_ZD_AGREE must be shown for the SAME `ch`.
2. **H_TXWIN per channel.** The per-transaction windowing, with H_QUIESCENT at every launch.
   The data side follows from the previous transaction's own separation. The request side is
   rule F/Fd (H_FF_DRAINED) for FASTFALL lines, and unchecked for the 21 plain bd_mux lines
   (8w).
3. **H_DERIVED.** 8w counts 376 of the 465 H_BUNDLE obligations as derived class (fork, link,
   steer, src outputs) with no tcheck row. Physically, each such bus is a wire from an upstream
   latch or a fork of another channel's bus. The cleanest discharge is to make tcheck emit an
   A-type row per derived channel (launch = upstream latch enable, data = latch Q to capture
   pins, req = through the fork/steer C-element). Then `BCert.dag` covers all 465 and `exempt`
   disappears.
   **A cleaner route (recommended).** Relax the Ops data fields: require `o.dat t = g (inputs at
   t)` only at the instants where the output channel `o` is busy, and likewise for the link's
   H_LATCH_OPEN/HOLD. The physical observation `obsCh` could then serve directly as the Ops
   trace, with no separate zero-delay `ch`. H_ZD_AGREE would become trivial, and H_BUNDLE would
   be exactly `held_net`.
   - The cell equations would reduce to per-transaction value equations. Those are what
     `sampled_eq_zd` (the output bus is `zdBus`) plus H_FN plus the inputs' own `sampled_eq_zd`
     give: the inputs are busy while the output is busy, by `JInv`/`FInv`/`SInv`.
   - Cost: re-checking that the capstone's operator proofs (`OpData`, `cell_op`) use the data
     fields only at busy instants of the output. I did not check this.
4. **H_RECV.** Kept as in 8w. Deriving it from H_CELLS would need a time-bounded
   `net_protocol` (`OpProto.ag` consumes `Held` at all times), and that would mean re-proving
   every `cell_proto`.
5. tcheck itself is in `formal/tools/tcheck`, not in this tree. Its verdict conjuncts are
   restated against this project's `checkArr_sound`/`potOK_sound` (as in 8w). The 8w gaps stand:
   - no row for umux21's select;
   - K/X4 failures on 11 muxes;
   - band-only failures on some routes.

## Fidelity

| model | grade | why |
|---|---|---|
| `Run` (per-arc bounded pure delay) | B | 10a's model: inertial filtering absent, zero-delay cell functions with delay on pins |
| `zdEval` / `run_settles` | A (proved) | exact consequence of `Run` |
| `TxWin` | B as a hypothesis | how tcheck's single-launch obligations are meant to tile a multi-token run; H_QUIESCENT per launch is the weak point |
| `BCert.exempt`, H_ZD_AGREE | C | open; see "What remains" |

## Check log (2026-10-29)

The lead's full `lake build` OOM-killed `CapstoneNetChk` and `CapstoneWitnessRun` (exit 137) and
never produced `CapstoneWitness*.olean`. So check.sh is given the witness chain too; it compiles
the chain into its private overlay, and no file of the chain is edited.

    cd /home/user/asyncfpga3/formal
    ./check.sh Formal/Net/CapstoneRefine.lean Formal/Net/CapstoneRefineWit.lean \
      Formal/Net/CapstoneRefineNet.lean Formal/Net/CapstoneWitnessData.lean \
      Formal/Net/CapstoneWitnessCells.lean Formal/Net/CapstoneWitnessWalk.lean \
      Formal/Net/CapstoneWitness.lean Formal/Net/CapstoneWitness3.lean \
      Formal/Net/CapstoneRefineGcd.lean

Output:

    [check] lean ... (all 9 files, no error)
    [audit] 4088 declarations checked
    [check] OK

Axioms are ⊆ {propext, Classical.choice, Quot.sound}. There is no sorry or native_decide;
`wcheck` and `bnet_reject` are kernel `decide`. An earlier run, `./check.sh
Formal/Timing/WinArray.lean Formal/Timing/Unroll.lean Formal/Net/CapstoneRefine.lean
Formal/Net/CapstoneRefineWit.lean`, gave `[audit] 469 declarations checked`, `[check] OK`.
Once the lake build has the oleans, the first three files alone suffice (`CapstoneRefine`,
`Wit`, `Net` import only WinArray, Unroll and Ops).
