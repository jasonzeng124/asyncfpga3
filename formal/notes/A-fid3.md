# A-fid3: formal model vs research board-fidelity GLS, per primitive (session 2026-10-29)

STATUS: in progress (probe Fid3, shard A). Research tip under test: origin/claude/research 6524fa3.

Plan:
1. Extract research cells/gls sources at 6524fa3 into tools-A/glsdiff3/run-1029/src (git archive, read-only).
2. Re-run the glsdiff3 suite (Kleene, channel fit, per-pin, seq X, CARRY4/latch SAF, FID_RESOLVE sweep)
   on the new sources; diff against out/ref_5d535d7.log / out/run.log (350f9be).
3. Read the new CARRY4 / SLICE_LATX / SLICE_FFX fid models (78de9c2, 923305d) and compare with Lean.
4. Per-primitive fidelity table + FID_RESOLVE threshold justification.
