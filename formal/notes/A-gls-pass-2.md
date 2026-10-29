# A-gls-pass-2: what a passing per-pin (GLS_MODEL=fid) GLS run implies

Probe GLSPass2, shard A, session 2026-10-29. STATUS: IN PROGRESS (plan written at start).
Files: formal/lean/Formal/Core/Delay/GLSFid.lean, formal/lean/Formal/Core/Delay/GLSPass2.lean,
formal/lean/Wip/GLSPass2/. Research tip read: origin/claude/research 6524fa3.

## Plan
1. GLSFid.lean: discrete-time (1 ps) model of FID_LUT6 (R:cells/gls/fid_core.vh:137-213):
   per-pin transport copy delayed d_k-1 (lines 152-158,172-182), zero-time mux tree
   (191-196), FID_SAMPLE 1 ps resample (122-131), FID_RESOLVE off (en=0, non-state LUT).
   Prove: fid LUT output = f(pins delayed by d_k) (per-pin transport), sample removes
   zero-width glitches; relation to SAF (equal when all d_k equal and Faithful).
2. GLSPass2.lean: a fid run is one point of the per-pin band; sufficient conditions for
   one/few corner runs to cover the band (monotone acyclic, rising inputs: two corner runs
   bracket); counterexamples (XOR skew hazard hidden at both corners, capture failure
   between corners), transport vs inertial channels.
