# C-8z5: H_NO_DEADLOCK'' -- spine localisation, no return-to-zero loop, narrowed obligation

Shard C, probe 8z5, 2026-10-29. Core Lean only (no Mathlib), no sorry/axiom/native_decide.
(Draft saved at 2h50m; final version below may extend it.)

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
