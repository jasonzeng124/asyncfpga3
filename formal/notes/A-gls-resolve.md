# A-gls-resolve: the trace semantics of research's FID_RESOLVE on the bd_c2 loop

Probe GLSResolve, shard A, session 2026-10-29. STATUS: IN PROGRESS (plan written, Lean being written).

Research side: `origin/claude/research` tip `6524fa3`, `cells/gls/fid_core.vh` (unchanged
since 5567170), read with `git show`, written `R:fid_core.vh:<line>`.

## Plan
1. `Formal/Core/Delay/GLSResolve.lean` (core Lean, imports GLSFid and B's CElemTiming read-only):
   the resolver as a per-step state machine on end-of-step values (`R:fid_core.vh:71-118`),
   the closed bd_c2 loop (f = LUT of delayed pins, feedback = o delayed by TLOOP).
2. Runt scenario (a = 1, rst = 0, b = pulse of width w): exact output for every w and every
   noise draw and every resolution time law (reject / back / commit).
3. What a passing run implies (no-runt => resolver is the identity), seed dependence, and
   counterexamples (transport loop oscillates forever: B's runt_oscillates; genuine pulses
   swallowed inside the ignore window).
4. B's hypotheses the resolver silently assumes.
5. iverilog cross-check on unmodified fid_core.vh (scratch).
