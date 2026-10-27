# C-8u: gcd_hw circuit liveness (capstone O5)

Shard C, probe 8u, 2026-10-27. Core Lean only, no sorry/axiom/native-decide.

**Status: PARTIAL.** gcd_hw circuit liveness is REDUCED to two named network obligations
(H_NO_DEADLOCK, H_FIRING_BOUND). Neither is proved. Everything else is proved: the
arbiter "key step", the ranking argument, and the bound together with the gcd value. The full
liveness theorem is NOT reached.

## Verdict

1. **Key step (arbiters): done.** `CapstoneLiveArb.gcd_hw_arb_settle`.
   - Hypotheses: 8r's H_CELLS, H_BUNDLE, H_START_ONCE, H_WALK, plus
     **H_ARB_UNCONTESTED_BOUNDED `H`**. That last one is a delay bound for an arbiter grant
     *only when the other request is low*. Nothing is assumed about a contested arbiter.
   - Conclusion: every one of the 9 gcd_hw arbiter stages obeys the **full** bounded law
     `ArbSettle H`. Whenever a grant is excited to rise or fall for `H + 1` ticks, it does so.
     So no arbitration in gcd_hw ever needs unbounded (metastability-resolution) time.
   - Proof: `gcd_hw_never_contested` (8q/8r's no-free-contention result, restated as "the
     contested state (both requests high, no grant held) never occurs") and
     `settle_of_uncontended`.
   - Negative control (`stall_cell`, `stall_unc`, `stall_contested`, `stall_not_settle`): a
     trace that meets the `CM.AMerge` cell model and H_ARB_UNCONTESTED_BOUNDED for every `H`,
     in which both requests stay high from tick 1 and no grant ever rises. So the uncontested
     bound alone gives nothing under contest, and 8r's result is a necessary input.
2. **Ranking argument: done, generic.** `CapstoneLiveRank.rank_live`.
   - Hypotheses:
     - H_FROZEN_QUIET (a state unchanged for `H + 1` ticks is quiescent);
     - H_NO_DEADLOCK (before the goal the state is not quiescent);
     - H_FIRING_BOUND `N` (before the goal at most `N` ticks change the state).
   - Conclusion: the goal holds by `(N + 1)(H + 1)`.
   - No fairness, no persistence, no SI serialisation.
   - For inertial gate networks (`Bridge.Timed`, every `hi ≤ H`), H_FROZEN_QUIET is *proved*
     (`timed_frozen_quiet`). This gives `timed_rank_live`.
   - Non-vacuity: `timed_rank_unit`, a 2-gate buffer chain at unit delay.
3. **gcd_hw instance: reduction proved.** `CapstoneLive.gcd_hw_live`.
   - Hypotheses: H_CELLS (as `CellI`, 8m's `Cell` with the internal traces explicit),
     H_BUNDLE, H_START_ONCE, H_WALK, **H_BOUNDED_DELAY `H`** (every non-arbitrating gate),
     **H_ARB_UNCONTESTED_BOUNDED `H`** (the 9 arbiter stages), **H_NO_DEADLOCK** and
     **H_FIRING_BOUND `N`**.
   - Conclusion: the circuit closes its first `out0` token at some step `e < (N+1)(H+1)`, and
     that token's value is `Nat.gcd a b`.
   - `frozen_quiet` is H_FROZEN_QUIET for the whole 465-channel network, arbiters included.
     It is where the key step enters: without `gcd_hw_arb_settle`, a frozen state could hide
     an excited but contested arbiter.
4. **Spine part of H_FIRING_BOUND: done.** `CapstoneLiveSpine.gcd_hw_spine_offers_bounded`.
   - Hypotheses: as 8r, plus **H_WALK_ENDS `L`** (the token-level spine walk stops after `L`
     steps: a token-run property, decidable per input, checked by `Wip/C8r/walkcheck.py` on
     32 vectors with up to 821 steps, not proved in Lean).
   - Conclusion: every one of the 67 spine channels offers at most `(walk σ L).W c ≤ L`
     tokens, and its request makes at most `2L + 1` transitions.
   - `gcd_hw_spine_done`: once the circuit has caught up with the ended walk, no spine request
     ever rises again.

The bound, as asked for: `(N + 1)(H + 1)` ticks. `H` is the per-gate delay bound. `N` bounds
the state-changing ticks before the first `out0` close. Writing `N` as a function of the token
run's length and the network size is exactly the open H_FIRING_BOUND. The spine contributes at
most `67 · (2L + 1)` request transitions (and as many acknowledge transitions). Data channels,
sources and internal nodes are unbounded in Lean.

## Run

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    FORMAL_SLOT_CWD=$PWD ../slot.sh lake build Formal.Net.CapstoneLiveRank Formal.Net.CapstoneLiveArb \
      Formal.Net.CapstoneLiveSpine Formal.Net.CapstoneLive
    FORMAL_SLOT_CWD=$PWD ../slot.sh lake env lean Wip/C8u/Axioms.lean   # prints axioms
    cd .. && ./check.sh Formal/Net/CapstoneLiveRank.lean Formal/Net/CapstoneLiveArb.lean \
      Formal/Net/CapstoneLiveSpine.lean Formal/Net/CapstoneLive.lean

Results: see "Check results" at the end.

The lead must add the 4 modules to `Formal.lean`. I do not own that file.

## Files

| file | contents |
|---|---|
| `formal/lean/Formal/Net/CapstoneLiveRank.lean` | `cnt_add_le`, `const_of_unmarked`, `window_change`, **`rank_live`**; `QuietS`, `chT`, `chT_false`, **`timed_frozen_quiet`**, **`timed_rank_live`**; `buf2`, `buf2_trace`, **`timed_rank_unit`**, `timed_rank_unit_at` |
| `formal/lean/Formal/Net/CapstoneLiveArb.lean` | `ex1`, `ex2`, `Win`, `Ev`, `Contested`, `ArbUnc` (H_ARB_UNCONTESTED_BOUNDED), `ArbSettle`, **`settle_of_uncontended`**, `never_contested_iff`, **`arb_frozen_quiet`**, **`gcd_hw_never_contested`**, **`gcd_hw_arb_settle`**, negative control `stall_cell`, `stall_unc`, `stall_contested`, `stall_not_settle` |
| `formal/lean/Formal/Net/CapstoneLiveSpine.lean` | `walk_stuck`, `W_mono`, `W_le`, `W_le_end`, `trans_le`, **`gcd_hw_spine_offers_bounded`**, **`gcd_hw_spine_done`** |
| `formal/lean/Formal/Net/CapstoneLive.lean` | `GS`, `gsAt`, `Gate`, `gatesK`, `grantsK`, `BndG` (H_BOUNDED_DELAY), `Quiet`, `CellI`, `cellI_cell`, `grants_bnd`, `bnd_frozen`, **`frozen_quiet`**, `first_ev`, `chG`, `chG_false`, **`gcd_hw_live`** |
| `formal/lean/Wip/C8u/Axioms.lean` | `#print axioms` only; proves nothing |

## The hypotheses, named

| id | statement (Lean) | grade | test |
|---|---|---|---|
| H_CELLS, H_BUNDLE, H_START_ONCE, H_WALK | as C-8r (`CellI` = `Cell` with internal traces named) | as C-8r | as C-8r |
| **H_BOUNDED_DELAY `H`** | `BndG H`: a gate excited toward `v` on all of `[t, t+H]` shows `v` somewhere in it. One `Gate` per output of every SI model gate (fork wires and ack C-tree; join req C-element and ack wires; steer LUTs and ack OR; mux joins `j0/j1`, `z_req`, acks; 3-way mux likewise; amerge `z_req` (rise guarded by both input acks low, as H_AMERGE_RTZ), acks; link controller `ctlB`, `ack_in`, `req_out`; src LUT1; sink wire) | B. It is the settle half of C-8d/8n's inertial channel. `H` must cover each lumped gate: a matched delay line plus OR (H_DELAY_LUMPED) counts as one gate whose `H` is the line's slow-max | GLS step response per lumped gate at the slow corner gives `H`; prjxray slow-max sums are the static estimate |
| **H_ARB_UNCONTESTED_BOUNDED `H`** | `ArbUnc H`: a grant rises within the window if, on all of it, its own request is high, the other grant low, `A0` low AND the other request low; it falls within the window if its request is low on all of it | B. With the other request low, the arbiter is a plain combinational path (B's `gr1_eq`/`gr2_eq`, settled `q`). It says nothing about a contest | GLS of `bd_arbiter` with one request only: grant latency ≤ `H` at both corners |
| **H_NO_DEADLOCK** | `∀ t, #out0 closes before t = 0 → ¬ Quiet (gsAt ch itr t)` | **OPEN proof obligation**, not a silicon hypothesis | none needed once proved; the board's gcd results test it end to end |
| **H_FIRING_BOUND `N`** | `∀ T, #out0 closes before T = 0 → #state-changing ticks before T ≤ N` | **OPEN proof obligation** (spine part proved under H_WALK_ENDS) | as above |
| H_WALK_ENDS `L` (spine bound only) | `(walk (σY a b y) L).cur = none` | token-level, decidable per input; `walkcheck.py` on 32 vectors | `python3 Wip/C8r/walkcheck.py` |

H_BOUNDED_DELAY and H_CELLS are not shown consistent on gcd_hw. No run of the 465-channel
network meeting both was built. The guards in `gatesK` are copied from the SI models' fields,
so a unit-delay synchronous run of the SI models should meet both, but this is not mechanised.

## Why the arbiter step is the right shape

- On this fabric an arbiter has no bounded decision time (track 7). So "every gate settles
  within `H`" is false for the grant LUTs under contest, and a liveness proof that assumed it
  would be unsound for the chip.
- H_ARB_UNCONTESTED_BOUNDED assumes the bound only where the arbiter does not arbitrate.
- `gcd_hw_arb_settle` shows that this restricted bound is all gcd_hw ever uses, because its
  arbiters are never contested.
- The negative control shows that the restriction has teeth: in a contested run the grants may
  stay low forever while every assumed bound holds.
- What this rests on: 8q/8r's no-free-contention result, which needs H_START_ONCE. With a
  free-running `start` (8r's finding), a second invocation can contest a loop header, and then
  no bound exists.

## What remains for full O5, and the effort

1. **H_NO_DEADLOCK** (about 2-3 days). This is the global progress fact. The plan:
   - simulate the token LTS by the circuit, using 8r's walk as the control skeleton;
   - at each walk position `p` with `cur = some c`, show that the producer of `c` is
     eventually excited. That needs:
     - (a) the data and condition inputs of the joins and steers on the path have arrived. This
       is a data-side invariant: every non-spine channel's offers are the token run's history
       prefix, as in 8m's `Agree` but for counts;
     - (b) capacity: the output stage is empty. T5 gives at least 3 links per cycle, and under
       one spine token the return-to-zero wave has cleared (8o's two-front invariant, per loop
       ring);
     - (c) the arbiter case is covered by this probe.
   - Each local case is a `quiet`/`reach_step` argument as in 8n.
2. **H_FIRING_BOUND for non-spine channels** (about 1 day after 1).
   - Data channels: offers on each channel are bounded by the token run's history length
     (`|Hh a b y c|`) plus the link capacity in front of each blocked join.
   - The free-running `a`/`b` sources re-offer after each acknowledge. Their extra tokens are
     stopped by the first link chain whose consumer waits for a control token, so their count
     is bounded by the number of link stages on that chain (100 linked channels, 175 stages in
     total).
   - Internal nodes make a bounded number of transitions per channel handshake (at most 2 per
     gate per token).
   - With 1 this gives `N ≤ c · (Σ_c |Hh a b y c| + 175)` for a small constant `c`. That is the
     requested "token-run length × network size" form. It is not derived here.
3. **H_WALK and H_WALK_ENDS in Lean** (C-8r's estimate: about 1 day, token level).
4. **Consistency** of H_BOUNDED_DELAY with H_CELLS: a unit-delay witness run of the network
   (about 0.5 day, if the kernel can evaluate it; the run has thousands of steps).

## What it does NOT show

- It does not show that gcd_hw latches a value: `gcd_hw_live` assumes H_NO_DEADLOCK and
  H_FIRING_BOUND.
- No numeric bound for any concrete `(a, b)`: `N` is not computed.
- Nothing about repeated invocations: H_START_ONCE covers one.
- Nothing about the data path's timing. The bound is in "gate delays", with H_DATA_COMB as
  before.
- Nothing about metastability under contest. The point of the arbiter step is that gcd_hw
  never contests.

## Fidelity

| primitive | model here | fidelity |
|---|---|---|
| every non-arbiter gate | SI guard as excitation + settle bound `H` (`BndG`) | the settle half of C-8d's inertial channel; the lower bound / cause half is the SI field already in `CellI` |
| arbiter grant | settle bound only when uncontested (`ArbUnc`) | strictly weaker than any bounded-arbitration model; faithful to "no bounded resolution time" |
| matched delay + OR | one lumped gate (H_DELAY_LUMPED, as 8f/8n) | `H` must be at least the line's delay |
| data buses | part of the global state; changes counted in `N` | H_DATA_COMB, as before |

## Surprises

- The ranking argument needs **no persistence**. An excited gate whose excitation is withdrawn
  is harmless, because withdrawing it is itself a state change and is counted. So the
  non-persistent arbiter does not break the argument. Only an excited gate that may wait
  forever does, and that is exactly the contested arbiter.
- The whole liveness question reduces to a bound on the number of state changes plus
  non-quiescence. The arbiter's metastability is the only place where bounded delay per gate
  is not available, and 8r's no-contention result removes it cleanly. The hard remaining part
  is ordinary dataflow progress (H_NO_DEADLOCK), not arbitration.

## Check results (2026-10-27)

- `lake build` of the 4 modules: OK. Each new module takes about 3-7 s once its dependencies
  are built. Building the dependencies from scratch (CapstoneCut and its chain) took about
  25 min under contention from other probes.
- `./check.sh Formal/Net/CapstoneLiveRank.lean Formal/Net/CapstoneLiveArb.lean
  Formal/Net/CapstoneLiveSpine.lean Formal/Net/CapstoneLive.lean`:
  `[audit] 3591 declarations checked`, `[check] OK`, in 71 s.
- `Wip/C8u/Axioms.lean`:
  - every theorem uses a subset of {propext, Classical.choice, Quot.sound};
  - `arb_frozen_quiet` uses none;
  - `frozen_quiet`, `stall_cell` and `stall_not_settle` use propext only.
