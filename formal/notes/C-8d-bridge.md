# C-8d: bridge from SI interleavings to timed traces

## Verdict

**Works.** H_SI of probe 9a is discharged: for any persistent network of
gates, every discrete-time (Nat ps) timed trace, read at its change points, is
an SI run, so every SI invariant (Ring's wavefront count) and the SI deadlock
and liveness facts hold of timed traces. Applied to `Ring.lean`: timed safety,
liveness, bounded-window fairness and the N <= 2 / degenerate deadlocks of the
real `bd_c2n` ring, for every per-stage delay assignment. Wire delays: the
inter-stage forks may be non-isochronic (proved for N = 3, 4 in Lean, N = 5 in
Wip, N <= 5 by BFS), the feedback fork may NOT (counterexample: token lost).
Transport delay in the form of `Prelim.BoundedDelay` breaks SI reasoning
(counterexample). Core Lean only. About 2 h of work.

## What checks

    cd formal && ./check.sh Formal/Net/Bridge.lean Formal/Net/BridgeTransport.lean \
        Formal/Net/BridgeRing.lean Formal/Net/BridgeWire.lean
    # -> [audit] 524 declarations checked, [check] OK   (about 30 s CPU)
    # axiom listing of the main theorems (propext, Classical.choice, Quot.sound only):
    cd formal/lean && export PATH=$HOME/.elan/bin:$PATH LEAN_PATH=$PWD/.lake/build/lib/lean
    ../slot.sh lean Wip/C8d/Axioms.lean
    # N = 5 certificate (32768 states, about 2 min CPU; checks, but left out of Formal/ for time):
    ../slot.sh lean Wip/C8d/Fork5.lean

`decide +kernel` is used for the certificate checks: it is kernel evaluation,
not `native_decide` (no `Lean.ofReduceBool`; the audit passes).

## Files

* `formal/lean/Formal/Net/Bridge.lean`: generic network, SI semantics, timed
  semantics, the bridge, liveness, non-vacuity, converse.
* `formal/lean/Formal/Net/BridgeTransport.lean`: transport counterexample.
* `formal/lean/Formal/Net/BridgeRing.lean`: Ring.lean, timed.
* `formal/lean/Formal/Net/BridgeWire.lean`: wires as buffer gates (forks and
  feedback), certificate checker.
* `formal/lean/Wip/C8d/Axioms.lean` (audit), `Wip/C8d/Fork5.lean` (N = 5).
* Python BFS used to produce the reachable-set certificates and to explore
  N <= 5: scratch only (the certificates are checked by the kernel, so a wrong
  one makes the check fail; it cannot prove anything false).

## Model

* `Net`: gates `0..n-1`, gate `i` drives node `i`, `f i : State -> Bool` reads
  the current node values. For the ring, `f i` is `Ring.gate n K false`, that
  is, `lutB` of the verbatim INIT of `bd_c2n` / `bd_c2n_set` (shard B's
  `CElemFn`), in run mode.
* SI semantics: `excited`, `fire`, `Reach`, `Run`, `Persistent` (every
  reachable state: firing `j` keeps every other excited `i` excited).
* Timed trace `x : Nat -> State`. Gate `i` = zero-delay function
  `e_i t = f i (x t)` followed by a delay channel to node `i`. Two channels:
  - `Inertial lo hi e o`: an output change at `t -> t+1` needs `e` equal to the
    new value on all of `[t+1-lo, t]` (`lo >= 1`); `settle`: `e` stable on
    `[t-hi, t]` implies `o t = e t`.
  - `NoOvertake hi e o` (weaker): an output change delivers a value `e` had at
    some `t'` after the previous output change (`o` constant on `[t', t]`),
    plus the same `settle`. `Inertial.noOvertake` proves inertial implies it.
* `Timed N lo hi x` (inertial) and `TimedF N hi x` (no overtaking): every gate
  obeys its channel; nodes `>= n` never change.

### Which delay channel, and why
The question was "inertial or bounded [lo, hi]; LUT + route is closer to pure
delay, which passes runts". Answer, proved:
1. Pulse filtering is not needed. The proof (`goodF`) uses only "no
   overtaking": in a persistent network an excitation is never withdrawn
   before the gate fires, so `e_i` has no runt for the channel to pass or
   filter. The channel only has to not deliver an OLD value of `e_i` after a
   newer change of the output.
2. `Prelim.BoundedDelay` (H_BOUNDED_DELAY as written: each output change
   copies `e` from some `d in [lo, hi]` ticks ago) violates this.
   `transport_breaks_si`: a persistent 4-gate network (source, buffer, SR
   latch, "fell-after-set" detector), every gate `BoundedDelay 1 4`, reaches
   at t = 5 a state no SI run reaches (`g3 = 1`, SI invariant `g3 = 0`,
   `cx_reach_g3`). The buffer rises (delay 1), then falls by replaying the
   stale `0` from t = 0 (delay 4), then rises again: an output runt with no
   input pulse. Under any inertial or no-overtaking bounds the same network
   keeps `g3 = 0` (`cx_inertial_safe`). So probe-level advice: do not use
   `BoundedDelay` for SI-style reasoning. It is a relation that allows edge
   reordering, which is not physical for one driver and route: in CMOS, edges
   of one net that come too close annihilate (pulse shrinks and vanishes,
   the involution-channel behaviour); they do not swap order.
3. Fixed transport delay (`o(t) = e(t-d)`) and FIFO variable delay: these keep
   edge order, so they are the physical case. I did not prove them to be
   `NoOvertake` traces in a persistent network (it needs an induction on the
   trace like `goodF`; the argument: `e_i` pulses in a persistent network last
   at least until the output fires, so a FIFO channel never has a stale edge
   queued behind a fresh one). Open, about 1-2 h.
4. Fidelity: H_NO_OVERTAKE for one LUT output + route is plausible
   (buffered pips; one driver per net). It is testable in GLS (pulse train of
   decreasing width through a LUT + long route at the slow and fast corners;
   check the output edge sequence is a subsequence of the input's, in order)
   and on the board (ring oscillator with an injected narrow pulse). The SDF
   GLS in iverilog uses per-edge rise/fall delays with inertial cancellation,
   so it satisfies NoOvertake by construction; it says nothing about silicon.

### Wire assumption (H_ISO) and what happens without it
`e_i t = f i (x t)`: every reader of node `j` sees `x t j` at the same
instant (isochronic forks). On the fabric each fork branch is a separately
routed wire. `BridgeWire.lean` makes chosen branches buffer gates of their
own (each its own channel, own bounds). That is another network; the bridge
applies to it iff it is persistent, i.e. iff the circuit is speed-independent
with those wires explicit (delay-insensitive on those forks).
* `forkNet n K`: node `c_i` with two branches, `u_i` (to stage i+1's `a` pin)
  and `v_i` (to stage i-1's `b` pin). Feedback still isochronic. BFS: N = 3,
  4, 5 persistent, D = 2 in all reachable states (48 / 192 / 640 states), no
  deadlock. Lean: kernel-checked certificate for N = 3 and N = 4
  (`fork3_check`, `fork4_check`, soundness `check_sound`), corollaries
  `timed_fork3`, `timed_fork4`: one loop token at every ps and some LUT or
  wire toggles within its own upper bound, for EVERY independent no-overtaking
  bound assignment to the N LUTs and 2N wires. N = 5 checks in
  `Wip/C8d/Fork5.lean`. General N: OPEN (needs a hand invariant over
  `c, u, v`; estimate 2-4 h). Meaning: the inter-stage forks of the ring are
  acknowledged (a node cannot move again before both branches have caught
  up), so routing skew between them is harmless.
* `fbNet n K`: the feedback branch `O -> I2` is a buffer `w_i`. NOT
  persistent (`fb3_not_persistent`). `fb3_token_lost`: run `[c1, c0, c1, w0]`
  from reset (N = 3, K = 1) ends in a dead all-zero ring with no wavefront
  (BFS also finds token duplication, D = 4, for N = 4). `fb3_timed_token_lost`:
  this run is an inertial timed trace with every LUT and wire in `[1, 4]`
  (via `realize`). Mechanism: c1 sets, c0 answers, c1's LUT now sees the hold
  input `a = b = 0` while its I2 pin still carries the old q = 0, so it
  reverts. So the feedback fork must be isochronic RELATIVE to the
  neighbour's response: feedback route delay < response of the neighbour
  stage (its LUT + both inter-stage routes). That is H_FB_SETTLED, and it is
  exactly the timing condition probe 5b (`CElemTiming`) derives for the
  feedback LUT. It is discharged by timing, not by SI.

### Other hypotheses carried by the timed ring theorems
* H_RESET_CLEAN (`x 0 = resetState K`): as in Ring.lean.
* H_ATOMIC_LUT: the LUT is one Boolean function of its pins at one instant
  (`e_i t = f i (x t)`). Inside the LUT, a multi-input change goes through the
  mux tree. In the ring, `a` and `b` of one stage can change concurrently
  (`c_{i-1}` and `c_{i+1}` both excited). By hand: for the transition
  `(a, b) = (q, !q) -> (!q, q)`, every monotone path, including Kleene X
  intermediates, gives `q, X, !q` and never returns to `q` (no dynamic
  hazard). Not yet a Lean theorem (one `decide` over `c2nK`, about 15 min);
  shard B's single-input-change results cover the rest.
* `settle` with per-gate `hi`: used only for liveness (`fires_within`).

## Theorems proved (namespaces under `Formal.Net.Bridge`)

Generic (`Bridge.lean`):
* `run_of_excited`: any duplicate-free list of gates excited in a reachable
  state is an SI run, in any order (persistence).
* `step_run` / `step_runF`: the simultaneous changes at one tick, serialized,
  are an SI run ending in the next state.
* `goodF`, `timed_reach(F)`: every timed state is SI-reachable.
* `timed_run(F)`: the change points on `[t, t+m)` concatenated are one SI run
  from `x t` to `x (t+m)`.
* `timed_invariant(F)`: every SI state invariant holds at every ps.
* `timed_frozen` (inertial, no persistence needed): a dead state is never left.
* `fires_within(F)`: an excited gate fires within its `hi`.
* `inertial_bounded`: Inertial refines `Prelim.BoundedDelay`.
  `Inertial.noOvertake`, `Timed.toF`.
* `unit_timed`: non-vacuity (unit-delay trace is inertial `[1, 1]`).
* `realize`: a finite SI run ending in deadlock is an inertial trace `[1, H]`.

Transport (`BridgeTransport.lean`): `transport_breaks_si`, `cx_persistent`,
`cx_reach_g3`, `cx_bounded`, `cx_inertial_safe`.

Ring (`BridgeRing.lean`, all for every per-stage bound assignment):
* `ring_persistent` (any N, from Ring.persistent / dead_of_le_two).
* `timed_ring_safe`: D = 2 at every ps (N >= 3, 0 < K < N).
* `timed_ring_live`: some stage toggles within `hi` of every t.
* `timed_ring_every_stage`: every stage toggles in every window of
  `(N(N-1)+1)·H` ps, `H >= hi i` (from `fair_window`).
* `timed_ring_k_tokens`: D = 2k, N >= 2k+1: never stuck.
* `timed_ring_dead` (N <= 2: frozen from any state), `timed_ring_degenerate`
  (K = 0 or K >= N: frozen at reset).

Wires (`BridgeWire.lean`): `check_sound`, `frame_mask`, `fork3_check`,
`fork4_check`, `fork3_persistent`, `fork4_persistent`, `timed_fork_of`,
`timed_fork3`, `timed_fork4`, `fb3_not_persistent`, `fb3_token_lost`,
`fb3_timed_token_lost`.

## Open goals

1. `forkNet` persistence for all N (have N = 3, 4 claimed, 5 in Wip).
2. FIFO / fixed transport traces of persistent networks are `NoOvertake`
   traces (so the bridge covers pure delay too).
3. H_ATOMIC_LUT for the ring's two-input transition, Kleene (`decide`).
4. Bounds in ps: the window `(N(N-1)+1)·H` is loose; the real period is
   about `N·(stage delay)`. A tighter timed bound needs a timed argument (not
   just the SI count).
5. Port to shard A's `Formal/Core/` (Mathlib, real time) when it settles.
   Discrete Nat time is enough here: nothing depends on the tick size.

## What it buys the project

Probe 9a's "ring needs 3 stages" and k-token results are now statements about
timed behaviour with arbitrary per-stage delays, under named hypotheses
(H_ISO on feedback only, H_NO_OVERTAKE, H_RESET_CLEAN, H_ATOMIC_LUT). It shows
which fabric facts the SI proofs actually rely on: edge order on a net, and
feedback faster than the neighbour, NOT pulse filtering and NOT isochronic
inter-stage forks. The generic bridge (`Bridge.lean`) applies to any other
persistent network (probe 8a's handshake, Muller pipelines), and
`check_sound` is a reusable small-model persistence checker.
