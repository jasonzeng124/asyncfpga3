# C-9d: the ring rule from bdc's reset, and on bounded-delay timed traces

Shard C, probe 9d, 2026-10-29. Core Lean only, no Mathlib. No sorry, axiom or native_decide.
`decide +kernel` is used only for the certificates. The track-9 verdict left two gaps, and
this probe closes both, within the scope stated below.

## Verdict

- **(a) H_ONE_TOKEN: works for N <= 5 links.** bdc's reset leaves every ring empty: every
  ring cell clears on rst. That is proved from the INITs, and a drift scan of the emitted
  gcd and collatz agrees. A closed link ring therefore holds no token and stays frozen on
  every timed trace. The token comes in through the loop entry. For the loop shape bdc emits
  (`bd_mux` -> N `bd_link` controllers -> `bd_steer` -> back to the mux), with real LUTs, an
  all-zero reset and one start token, a kernel-checked reachable set shows:
  - N = 3, 4, 5: exactly one four-phase token (D = 2) while the loop runs, no deadlock, and
    speed-independence;
  - N = 1, 2: an explicit run deadlocks with the token inside.
  So the mux and the steer add no storage. The environment hypotheses are listed below.
- **(b) Timed lift: works.**
  - `timed_ring_three`: the rule as one timed statement, both directions, for every
    per-stage inertial bound.
  - The same results on bounded **pure FIFO** delay traces, which is Core's transport
    channel transcribed to discrete time (`pure_noOvertake`; this closes 8d's open goal 2).
  - Period lower bounds: rise to rise is at least `N·dmin` (and at least `6·dmin` when
    N = 3). These are tight, with unit-delay witnesses.
  - Upper bound: at most `2N·dmax`, from 8o.
  - A pulse filter cannot kill a live ring: no runt exists on any stage's LUT output
    (`ring_no_runt`).

## Files and how to run

| file | contents |
|---|---|
| `formal/lean/Formal/Net/RingTimed.lean` | `timed_ring_three`, `timed_ring_never`, change counts `nc`, `balance_t`, `cause_window`, `cause_counts`, `fwd`, `bwd`, `iter_fwd`, `iter_bwd`, `window_fwd`, `window_bwd`, `window_loc`, `gap_two`, `gap_three`, `gap_two_n3`, `gap_three_reset`, `ring_no_runt`, `tight_n3/4/5`, `unit_hyps` |
| `formal/lean/Formal/Net/RingTimedPure.lean` | `PureFifo`, `TimedP`, `nchg_read`, `Alt`, `alt_step`, `fire_of_alt`, `goodP`, **`pure_noOvertake`**, `unit_pure`, `ring_pure_safe_live`, `ring_pure_dead` |
| `formal/lean/Formal/Net/RingReset.lean` | reset values of the control cells from the INITs (`*_rst_clear`); `bdc_closed_ring_empty`; the loop-ring transition system (`gateVal`, `envSucc`, `succ`, `Reach`); `goodB`/`Good`; `cert_sound`, `cert_good`, `good_of`, `reach_path`, `stuck_of` |
| `formal/lean/Formal/Net/RingResetCert.lean` (generated) | `L3`, `L4`, `L5` with `L*_cert` and **`loop3_good`, `loop4_good`, `loop5_good`**; `P1`, `P2` with **`loop1_stuck`, `loop2_stuck`**; `W3` with `loop3_exits` |
| `formal/lean/Wip/C9d/py/loop.py` | first exploration of the loop ring (two env variants) |
| `formal/lean/Wip/C9d/py/loopgen.py`, `gencert.py`, `props.py` | bit-vector model (same semantics as the Lean), certificate generator, property check |
| `formal/lean/Wip/C9d/py/period.py` | unit-delay and random-delay simulation of the ring period |
| `formal/lean/Wip/C9d/py/resetscan.py` | drift check: reset value of every rst-pinned LUT reachable from an emitted design |

Run:

    cd /home/user/asyncfpga3/formal
    ./check.sh Formal/Net/RingTimed.lean Formal/Net/RingTimedPure.lean \
               Formal/Net/RingReset.lean Formal/Net/RingResetCert.lean
    # regenerate the certificate (BFS, untrusted; the kernel re-checks it):
    cd lean/Wip/C9d/py && python3 gencert.py ../../../Formal/Net/RingResetCert.lean
    python3 props.py        # Python view of the same properties
    python3 period.py       # period simulation
    # drift check against the emitter:
    cd /home/user/asyncfpga3 && python3 bdc/emit.py cloud/fixtures/frontend/gcd/comp/handshake_transformed.mlir -o /tmp/gcd.v
    python3 formal/lean/Wip/C9d/py/resetscan.py /tmp/gcd.v

The lead needs to add four modules to `Formal.lean`: `Formal.Net.RingTimed`,
`Formal.Net.RingTimedPure`, `Formal.Net.RingReset` and `Formal.Net.RingResetCert`. I do not
own that file.

## (a) What bdc's reset puts in a ring

### The reset values, from the INITs (`RingReset.lean`, section 1)
- bdc emits every link as `bd_link_ctl` = `bd_c2n` (INIT `0x00B2_00B2_00B2_00B2`, rst on I3).
  It never instantiates `bd_c2n_set` or `bd_c2_set`. The `bd_ce.v` header calls `bd_c2_set`
  "the loop's select token", but bdc does not use it.
- Proved by `decide` on the verbatim INITs, for every value of the other pins: under
  `rst = 1`, each of the following drives 0:
  - `bd_c2n`, `bd_c2`, `bd_c3`, `bd_c4`;
  - `bd_mux`'s two join LUTs (`uj0` `0xAE08`, `uj1` `0xEA80`, rst on I4).
- The only cell that comes up at 1 is the arbiter's state node. Its standalone form is
  `bd_c2n_set` in `bd_arbcell`; the inline LUT6_2 in `bd_arbiter` has INIT
  `0xFFF0_FFB2_ACAC_ACAC`. Per `bd_arb.v` it decides only who wins the first tie. It is not
  a handshake node on any ring.
- `resetscan.py` on the gcd and collatz that bdc emits today walks every module the design
  instantiates. No `*_set` cell is reachable. Every rst-pinned LUT clears to 0 except that
  arbiter state node. The scan also lists `bd_link_dctl` (also clears): it is only
  selected under `` `define BD_LINK_DC ``, and the scan does not resolve `ifdef`s.
- **`bdc_closed_ring_empty`**: for any N, with rst held every stage of the closed ring
  drives 0. The release state `resetState 0` has `D = 0`. Every inertial timed trace from
  it is constant: 8d's `timed_ring_degenerate` at K = 0.

**H_ONE_TOKEN is not a property of the reset state.** The `0 < K < N` reset that 9a and
tb_ring.v use (stages coming up holding) does not occur in emitted designs.

### The loop ring with its entry (`RingReset.lean` section 2, `RingResetCert.lean`)

**Model.** It is the cycle emit.py's comment says was measured ("mux -> steer -> storage ->
mux"), with every gate its real LUT (in run mode):

| gate | cell, INIT | inputs |
|---|---|---|
| `c_i`, i < N | `bd_c2n`, `0x00B2…` | a = `c_{i-1}` (for `c_0`: the mux `z_req`), b = `c_{i+1}` (for `c_{N-1}`: the steer ack) |
| `j0` | `bd_mux` `uj0`, `0xAE08` | `x_req`, `ctl_req`, `s`, feedback |
| `j1` | `bd_mux` `uj1`, `0xEA80` | `y_req` = steer `req1`, `ctl_req`, `s`, feedback |
| `z_req` | mux OR, `0xE` | `j0`, `j1` |
| `x_ack`, `y_ack` | `bd_c2`, `0x00E8…` | `j0` / `j1`, and `z_ack` = `c_0` |
| `ctl_req` | `bd_src` LUT1, `0x1` | `ctl_ack` = `z_ack` = `c_0` |
| `req1`, `req0` | `bd_steer` LUT6_2, `0x8888888822222222` (O6, O5) | `c_{N-1}`, steer select |
| `ack0` | `bd_snk` (`ack = req`) | `req0` |
| steer ack | OR, `0xE` | `ack0`, `y_ack` |

- The `bd_delay` chain behind the mux OR is folded into the OR gate (H_DELAY_AS_GATE).
- Semantics are SI: one gate at a time, plus environment moves.

**Environment (named hypotheses; they are exactly `envSucc`):**
- **H_START_ONCE:**
  - `x_req` rises once, when `x_ack = 0`;
  - it falls after `x_ack` rises;
  - it never rises again.
- **H_CTL_ENV:**
  - the mux control channel is a free `bd_src`;
  - its select level is 0 for the entry transaction;
  - it switches to 1 once, only after `x_req` has fallen and while the mux is idle (both
    joins, the OR and both acks at 0).
- **H_EXIT_ENV:**
  - the steer select is 1;
  - it may switch to 0 once, only while the steer is idle (`c_{N-1}`, both branch
    requests, the sink ack and the steer ack at 0) and after the loop has closed;
  - runs that never exit are included.

**Theorems.**
- `loop3_good`, `loop4_good`, `loop5_good`: every state reachable from bdc's reset (all LUT
  nodes 0) satisfies `Good N s`:
  - `two`: the link ring carries `D ∈ {0, 2}`;
  - `preEntry`: before the entry token is offered, `D = 0`;
  - `looping`: while the token loops (mux select 1, not exited), `D = 2` (exactly one
    four-phase token) and some gate is excited, without any help from the environment;
  - `stop`: the only states with no move at all are after the exit with `D = 0`, meaning
    the token has left and the loop is empty again;
  - `persist`: no firing disables another excited gate, so the loop is speed-independent.
- Reachable states: 120 (N = 3), 192 (N = 4), 282 (N = 5).
- `loop3_exits` (non-vacuity): a run from reset takes the entry, closes the loop, takes the
  exit and ends with no move left and `D = 0`.
- `loop1_stuck`, `loop2_stuck`: from the same reset, an explicit run reaches a state with no
  excited gate and no allowed environment move, before any exit. That is a deadlock with the
  token inside (N = 1 stalls during the entry, N = 2 while looping).

**Plain statement.** For the loop shape bdc emits, with 3 to 5 links, in the SI semantics:
reset plus one start token gives exactly one token in the loop, the loop runs until the exit
is taken, and then it is empty. With 1 or 2 links it deadlocks. The mux and the steer add no
storage stage, which is what emit.py's comment claimed was measured.

**Not covered:**
- The real sources of the mux control token and the steer select. Those are the
  control_merge index ring and the loop condition's data path; here they are environment
  moves.
- Loops whose cycle carries other cells (fork, join, op cells).
- N > 5 for the loop. The closed-ring theorems are for every N.
- Timed traces of the loop. The environment moves are not gates, so 8d's bridge does not
  apply as is. The loop is persistent, so it would apply once the environment is modelled
  as persistent gates.
- Data latches.

**The k-token remark stands.** If a future bdc pipelines a loop with k tokens in flight,
the floor becomes 2k+1 (9a's `k_tokens`). This model has k = 1 by H_START_ONCE.

### What it means for the rule
The rule "3" now rests on three things:
1. bdc's cell choice: proved and scanned.
2. H_START_ONCE plus the two select hypotheses, per loop.
3. For the general shape, the composition claim that the other cells on a cycle add no
   storage. This is checked here for mux and steer at N <= 5.

The audit's caveat about H_START_ONCE for the rig (start re-offered after every result)
applies here too. The model allows exactly one entry. A second entry after the exit is the
same situation again from an empty loop, but that is not checked.

## (b) The rule on bounded-delay traces

### One timed statement (`RingTimed.lean`)
- **`timed_ring_three n K (0 < K < N)`:** the following holds iff `3 ≤ N`: for every
  per-stage bound `lo, hi` and every inertial timed trace from `resetState K`, after every
  instant some stage toggles within its upper bound.
  - `←` is 8d's `timed_ring_live`.
  - `→` uses the unit-delay trace (`unit_timed`), which exists for every network and is
    frozen for N <= 2.
  - `timed_ring_never` strengthens the dead side: for N <= 2, no trace ever toggles.
- **`ring_pure_safe_live` / `ring_pure_dead`:** the same on bounded pure FIFO delay traces.

### Which delay channels are covered
- Inertial `[lo, hi]` (`Bridge.Timed`): 8d.
- No-overtaking (`Bridge.TimedF`): 8d.
- **Bounded pure FIFO delay (`TimedP`), new.** This is Core's `DelayPure.Chan lo hi` in
  discrete time: a nondecreasing read map `σ` with ages in `[lo, hi]`; pulses may
  collapse, but edges never cross. It is transcribed, not imported, because Core uses
  Mathlib and shard C's closure stays Mathlib-free. The prehistory (`pre`) shows the
  output's own initial value.
- **`pure_noOvertake`:** in a persistent network, every `TimedP` trace is a `TimedF` trace,
  so it is an SI run. Every 8d, 9a and 9d `TimedF` result therefore holds for pure delay.
  The proof:
  - Output edges up to `t` number at most the input edges up to the read index
    (`nchg_read`, FIFO monotonicity).
  - Persistence keeps (input edges incl. the initial one) - (output edges) equal to the
    excitation in {0, 1} (`Alt`, `alt_step`).
  - Hence an output change at `t` finds the gate excited at `t` (`fire_of_alt`).
  - Non-vacuity: `unit_pure`.
- 8d's counterexample still stands: per-edge transport (`Prelim.BoundedDelay`) reorders
  edges and breaks SI. FIFO is the dividing line, and it is the physical one for one driver
  and route (A-delay-pure).

### Period and throughput (dmin = d <= every `lo i`, dmax = H >= every `hi i`)
Derived from max-plus causality on timed traces. `nc j u` is the number of changes of stage
`j` before `u`; `δ_i` is the wavefront at `i` at time 0.
- `balance_t`: 9a's balance law, timed.
- `cause_window`: an inertial change at `t` was preceded by `lo j` ticks of steady
  excitation.
- `fwd`: `nc j u ≤ nc (j-1) (u - lo j) + δ_j`.
- `bwd`: `nc j u + δ_(j+1) ≤ nc (j+1) (u - lo j) + 1`.
- Iterated round the ring, with D wavefronts at time 0:

| theorem | statement (any inertial trace, any D) |
|---|---|
| `window_fwd` | at most `D` changes of a stage in any `N·d` window |
| `window_bwd` | at most `N - D` changes in any `N·d` window |
| `window_loc` | at most 1 change in any `2·d` window |
| `gap_two` | two changes of a stage are at least `2·d` apart |
| `gap_three` (D = 2), `gap_three_reset` | three changes span at least `N·d`, so **rise to rise ≥ N·dmin** |
| `gap_two_n3` (N = 3, D = 2) | two changes at least `3·d` apart, so **rise to rise ≥ 6·dmin** |
| `tight_n3`, `tight_n4`, `tight_n5` | unit-delay witnesses meet `3d`, `2d` and `N·d` exactly |

- Lower bound per token: rise to rise is at least `N·dmin` for N >= 4 (at N = 4 the local
  bound `2·2d` gives the same 4d) and `6·dmin` for N = 3. This is the max-plus cycle mean
  `2·max(N/2, N/(N-2), 2)`, attained at unit delay (`period.py`: unit gaps 6, 4, 5, 6, 7, 8
  for N = 3..8).
- Upper bound: 8o's `OpsRingLive.ring_every_window_reset` says every stage changes in every
  `N·H` window, so rise to rise is at most **`2N·dmax`**. It is not imported here, because
  its olean was still building; it is cited.
- **Not proved: the exact cycle time.** The max-plus value `p·dmax` with `p = N` (N >= 4)
  or 6 (N = 3) is an asymptotic average, not a per-cycle bound. `period.py` with random
  per-event delays in [10, 30] gives one N = 4 cycle of 131 > 4·30 = 120 (averages
  94-163 stay below `p·30`). So "rise to rise ≤ p·dmax" is false cycle by cycle. A true
  per-cycle bound lies between `p·dmax` and 8o's `2N·dmax`. The average bound needs a
  potential (max-plus eigenvector) argument; I did not attempt it.
- These lower bounds are proved for inertial channels only (`Timed`, they use `lo`). For
  pure FIFO the same excitation window holds (the argument is in `fire_of_alt`'s counting),
  but I did not state the window theorems for `TimedP`.

### Can an inertial channel with pulse filtering kill a live ring (a runt)?
**No, under the ring's hypotheses (H_ISO forks, H_FB_SETTLED feedback, atomic LUT).**
- `ring_no_runt`: in every no-overtaking timed trace, once stage `j` is excited, its LUT
  output keeps the excited value until the stage changes. The input of the delay channel
  therefore never has a pulse that the output does not eventually follow. A filter of any
  width never swallows an excitation.
- Liveness (`timed_ring_live`) holds for every `[lo, hi]` with `lo ≤ hi`. With `lo > hi`
  the inertial relation admits no trace in which a stage toggles, so those theorems are
  vacuous there. Non-vacuity is shown at `lo = hi = 1`.
- The ways to get a runt are all outside these hypotheses, and they are already known:
  - A slow feedback wire. 8d's `fb3_timed_token_lost` is an inertial trace in [1, 4] in
    which the ring loses its token and dies. This is H_FB_SETTLED, discharged by timing
    (RT_FB), not by SI.
  - The LUT's mux tree on a two-pin change. Covered for the ring's only concurrent
    two-pin transition by 8d's Kleene lemma `ring_lut_two_input_monotone`.
  - Per-edge transport. Excluded by FIFO (see above).

## Hypotheses and non-vacuity

| hypothesis | where | non-vacuity / status |
|---|---|---|
| H_INERTIAL `Timed` (`lo i ≥ 1`) | `RingTimed` windows, `timed_ring_three` | `unit_timed`, `unit_hyps` (lo = hi = 1) |
| H_NO_OVERTAKE `TimedF` | `ring_no_runt`, `balance_t` | `Timed.toF` of the unit trace |
| H_PURE_FIFO `TimedP` | `RingTimedPure` | `unit_pure` |
| D = 2 at time 0 | `gap_three`, `gap_two_n3` | from H_RESET_CLEAN with 0 < K < N (`Ring.D_reset`), or from the loop entry (`loopN_good.looping`) |
| H_RESET_CLEAN, all-zero (bdc) | `bdc_closed_ring_empty`, loop `s0` | the reset values are proved; the reset width is shard B's C5 |
| H_START_ONCE, H_CTL_ENV, H_EXIT_ENV | `envSucc` | `loop3_exits`: a kernel-checked run from reset takes the entry, closes the loop (passes states with mux select 1), takes the exit and ends empty |
| H_DELAY_AS_GATE | mux OR + delay chain as one gate | a buffer chain is persistent; modelling each buffer separately is not checked |
| H_ISO, H_FB_SETTLED, atomic LUT | all ring statements (inherited from 8d) | as 8d |

## Effort and what it buys
- Buys:
  - 9a's rule now holds end to end in the digital model: bdc's reset, one start token,
    the loop shape with its mux and steer, timed traces with inertial or pure FIFO delay.
  - A tight lower period bound.
  - A proof that pulse filtering never matters for the ring.
- Remaining:
  - The loop for every N, by a hand invariant instead of a certificate: about 1 day. It
    should be the 9a wavefront argument with the mux and steer as a two-node "port".
  - The real control sources (control_merge index ring) in place of the environment
    moves: about 1-2 days, sharing work with 8u/8z.
  - The window theorems for `TimedP`: about 2 h.
  - The exact max-plus cycle time: about 1 day.
