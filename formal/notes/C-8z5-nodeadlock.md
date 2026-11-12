# C-8z5: H_NO_DEADLOCK'' -- spine localisation, no return-to-zero loop, narrowed obligation

Shard C, probe 8z5, 2026-10-29. Core Lean only (no Mathlib), no sorry/axiom/native_decide.
(Draft saved at 2h50m; the probe never committed. CLAIMED 2026-10-31 by the next C session: the
three files `CapstoneLiveNd5{Spine,Loop,}.lean` moved from Wip/_snapC to Formal/Net unchanged and
pass `./check.sh` there; Wip/C8z5/Neg.lean holds the negative controls.)

**Status: PARTIAL.** H_NO_DEADLOCK'' is **still OPEN**. What is new (kernel-checked):

1. `spine_local`: route B's spine case analysis on 8r's `Inv`, done. In every quiescent state
   the control walk has ended or is `Blocked` at a link / bjoin / arbiter output for an
   explicit local reason; it is never at a fork, a steer or `start`.
2. `gcd_hw_no_rtz_loops`: the "capacity" obstruction C-8z4 named (a whole loop stuck in
   return-to-zero waits, the cycle its buggy explorer reported) never occurs, at any tick of
   any run.
3. `nd2_iff_noblock`, `gcd_hw_live_final3`: H_NO_DEADLOCK'' is equivalent to `NoBlock`
   (refute the blocked configurations only), and liveness follows from `NoBlock`.
4. Two blocked sub-cases refuted: `link_chain_excl`, `gcd_hw_rtz_header`.

## Analysis 2026-10-31 (next C session; no new Lean)

Hand-tracing `Blocked` on gcd_hw's spine (59 operators; `Wip/C8z5/spine_ops.txt`):
- link outputs whose consumer chain is link -> link are refuted (`link_chain_excl`: 104, 185,
  241, 340, 383). The others (105/106-type: consumer link -> amerge, or the amerge itself) do NOT
  close by counts alone: following the waits forward, every chain I traced ends at a DATA-side
  wait -- the non-spine output of a spine forkG (e.g. 102 of fork 168) still acknowledged
  (return-to-zero pending), or not yet acknowledged, by its data consumer;
- bjoin-blocked = the condition token (from a compare unit) not yet offered: a data wait;
- arbiter-blocked reduces to the fork after `z` the same way.
So NoBlock is, in substance, liveness of the DATA side relative to the control token. Two routes:
1. a waits-for graph argument: quiescence gives every busy channel a wait edge to a neighbour;
   finiteness gives a cycle; each cycle (spine loops: `no_rtz_loop`; data loops through the muxes;
   reconvergent fork/join diamonds) must be refuted with count invariants -- many cycle shapes;
2. confluence: in a persistent (semimodular) interleaving system, a reachable dead state is
   reachable from every reachable state (diamond property), so ONE run per input that closes out0
   rules out every deadlock before the close (close counts are monotone). Needs: persistence of
   the mux input acknowledges (8z3's exception: their falling excitation can be withdrawn by the
   mux's own z_ack, depth one by `mux_out_not_mux`), a terminating interleaving run for EVERY
   input (a constructive schedule, e.g. the unit-delay run, proved to close out0 -- itself a
   liveness proof, but of ONE deterministic run), and the timed->interleaving bridge (8z4's
   `serial`, its `hex` premise unproved for gcd_hw). Route 2 looks shorter.
