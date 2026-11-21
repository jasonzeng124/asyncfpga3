# C-9a: "a ring needs three storage stages per simple cycle", proved

## Verdict

**Works.** The rule is proved for every N (not only N = 1..6), and the proof
shows where the 3 comes from: it is 2k+1 with k = 1 loop token. File
`formal/lean/Formal/Net/Ring.lean` (core Lean only plus shard B's
`Formal.Cells.CElemFn`; no sorry/axiom/native_decide). Built in about 1.5 h.

Run:

    cd formal && ./check.sh Formal/Net/Ring.lean     # -> [audit] 300 declarations checked, [check] OK
    # or, without Mathlib on the path:
    cd formal/lean && export PATH=$HOME/.elan/bin:$PATH LEAN_PATH=$PWD/.lake/build/lib/lean
    ../slot.sh lean -o .lake/build/lib/lean/Formal/Cells/CElemFn.olean Formal/Cells/CElemFn.lean
    ../slot.sh lean Formal/Net/Ring.lean

## Why the project believes the rule (sources)

* `bdc/emit.py` (comment above `RING_MIN_STAGES = 3`): "measured, not argued":
  `cells/tb/tb_ring.v` sweeps it on the frozen cells. The structural argument:
  close c_i = C(c_{i-1}, ~c_{i+1}) on two stages and each C-element sees x and
  ~x forever. "Occupancy is half a token per stage, so one token fills two
  stages and needs a third to move into." Mux/steer/fork/join are
  return-to-zero rendezvous and add no stages. The rule must hold on every
  SIMPLE cycle (gcd: an SCC with 34 stages still has a 1-stage control ring).
* `cells/tb/tb_ring.v`: a closed ring of `bd_c2n` (first K are `bd_c2n_set`),
  wired `.a(c[i-1]) .b(c[i+1])`; expects N=1,2 dead, N=3..6 live with K=1;
  K=0 and K=N dead; 0<K<N live.
* `cells/rtl/bd_link.v`, `cells/docs/LIBRARY.md`: the stage is `bd_link_ctl`,
  one `bd_c2n` LUT6 (INIT 0x00B2..., clears on rst); its node drives the latch
  enable, req_out and ack_in. A `_set` stage (`bd_c2n_set`, 0xFFB2...) comes up
  holding (node = 1).
* What the emitter actually builds: all ring links reset EMPTY (`bd_c2n`); the
  loop token enters from the loop entry through the header mux (`bd_c2_set` is
  for a loop's initial select token). See "fidelity gaps".

## Model (stage model and token meaning)

* State: one Bool per controller node c_i, i < N. Gate i is the real LUT
  (`c2nB`/`c2nsetB` = `lutB INIT [a,b,q,rst,0,0]`, shard B), proved equal in
  run mode to `ctl a b q` = set on a.~b, reset on ~a.b, hold on a tie
  (`c2n_run`, `c2nset_run`); under rst every gate drives its reset value
  whatever the inputs (`gate_rst`), so the release state is `resetState K`
  (stages i < K at 1).
* Transitions (H_SI): fire one excited gate at a time, any order.
* **Wavefront** `tok i := c_{i-1} ≠ c_i`. Gate i is excited iff wavefront at
  i and none at i+1 (`excited_tok`); firing moves it i -> i+1 (`tok_fire`).
  So the ring is a token-on-a-cycle system with D wavefronts. A four-phase
  data token is TWO wavefronts (its req rise and its req fall). The
  tb_ring reset state with 0<K<N has D = 2 for every such K (`D_reset`):
  one loop token. K = 0 (empty) and K >= N (all holding) have D = 0
  (`D_reset_degenerate`).
* Bubble: a stage with no wavefront. A latch is transparent while its node is
  1; "half a token per stage" = each stage holds one wavefront.

## Theorems proved (namespace `Formal.Net.Ring`)

* `dead_of_le_two`: N <= 2 -> no gate is excited in ANY state (prv i = nxt i,
  the C-element sees x and ~x). `reach_le_two`: nothing ever moves.
* `D_fire`, `D_reach` (**safety**): wavefront count invariant: tokens are never
  lost or duplicated. `ring_safe`: from reset (N>=3, 0<K<N), D = 2 forever.
* `live_iff`: for N >= 3, a state has an excited gate iff 0 < D < N.
* `persistent`: an excited gate is never disabled by another firing
  (semi-modularity: the ring is speed-independent / hazard-free under
  inertial gate delays).
* **`ring_three`**: for 0<K<N, (every state reachable from `resetState K`
  has an excited gate) <-> 3 <= N. Both directions.
* `ring_degenerate_dead`: K = 0 or K >= N -> dead at reset (tb_ring's ends).
* **`k_tokens`**: from ANY state with D = 2k, k >= 1: (every reachable state
  live) <-> 2k+1 <= N. `kState`/`D_kState`/`kState_live_iff` give a concrete
  reset pattern (stages 0,2,..,2k-2 set) with exactly k tokens, so it is not
  vacuous.
* **`fair_window`** / `every_stage_fires` (progress): any execution in which
  stage i never fires has at most N(N-1) transitions; so every window of
  N(N-1)+1 transitions fires every stage, under any interleaving. Proof by the
  exact balance law `balance`: firings(x) + [wavefront at x now] =
  firings(prv x) + [wavefront at x initially]. `extend`: from reset (N>=3) an
  execution can always be extended. Together: the ring circulates forever and
  every stage toggles infinitely often.
* N = 1..6, K = 1 instances as `example`s (the tb_ring length sweep).

## Results worth saying plainly

1. The minimum is **3 for one loop token, and 2k+1 for k tokens**. The
   true law is "live iff 0 < 2k < N" (wavefronts strictly between empty and
   full), so a ring that must hold k tokens concurrently needs 2k+1 stages,
   not 3. The project's one-token-per-loop invariant (`bdc/AUDIT.md`) is
   what makes 3 correct; any future pipelining of a loop (k > 1 tokens in
   flight) must raise RING_MIN_STAGES to 2k+1. Max live tokens on N stages:
   floor((N-1)/2).
2. tb_ring's "occupancy sweep" (K = 2, 3, 5 at N = 4, 6) does NOT vary the
   number of tokens: every 0<K<N reset carries exactly one token (two
   wavefronts at 0 and K). It varies only where the token's two edges start.
   The bench therefore never tested a 2-token ring; e.g. N=4 with stages 0,2
   set (k = 2, D = 4 = N) is dead, and N=5 with k=2 is live (`k_tokens`).
3. Failure mode for N <= 2 is deadlock (stable, nothing excited), not token
   loss/duplication: N <= 2 never moves at all from any state.
4. The comment in emit.py ("x and ~x permanently disagreeing") is exactly
   `prv_eq_nxt_of_le_two` + `dead_of_le_two`.

## Hypotheses and fidelity

* **LUT function**: real INITs via shard B's `lutB` (binary). Faithful as the
  LUT's settled function; glitch/Kleene behaviour is shard A/B's.
* **H_RESET_CLEAN**: rst held until all nodes settle; release yields
  `resetState K`. tb_ring's HOLD comment documents the failure when this is
  violated (power-up X latched). Testable in GLS by shortening HOLD; on the
  board by the existing reset sequencing.
* **H_SI** (one gate output changes at a time, any order, feedback settled =
  `H_FB_SETTLED` of probe 5a): under bounded inertial delays with no
  simultaneous changes every execution is an interleaving, so the deadlock
  result is delay-independent (a state with no excited gate is stable under any
  delay model) and liveness/progress hold for any delays in which an excited
  gate eventually fires (`persistent` guarantees no excitation is withdrawn,
  so no runt pulses). Simultaneous changes are not modelled; they cannot
  break the deadlock result and the persistence lemma makes them benign for
  the others, but that is argued, not proved. Testable: tb_ring under routed
  GLS (each length, random seeds), and on the board by toggle counting.

## Fidelity gaps / not covered

* **Only the controller ring is modelled.** Mux/steer/fork/join in the
  cycle are assumed to add no storage (emit.py's claim, AUDIT.md's rendezvous
  argument). That they are transparent to the ring argument is a composition
  claim (track 8), not proved here.
* **How the token enters.** Emitted rings reset empty (D = 0, dead by
  `ring_degenerate_dead`); the token is injected via the loop header mux.
  The theorems apply from the moment the ring closes holding one four-phase
  token (D = 2; `k_tokens` covers any state with D = 2k). That the
  injection produces exactly D = 2 is H_ONE_TOKEN, unproved here; it needs
  the mux model (track 8).
* Data latches are not modelled (only control); bundling is track 6.
* `bd_link_dc` (decoupled, one token per stage, experimental/not production)
  is not covered; its floor would differ (likely k+1) and it is not SI.

## Effort to finish / what it buys

* Done for the controller ring. Linking to the mux/entry (H_ONE_TOKEN) and to
  the trace semantics of `Formal.Net.Prelim` (bounded delays) is ~1-2 days
  each once track 8 has a mux model.
* Buys: the decided rule now has a proof and a precise statement (2k+1),
  and a cheap obligation for `ring_depths()`: it is correct exactly as long
  as the one-token-per-loop invariant holds. It also flags that tb_ring's
  occupancy sweep is weaker than it reads.
