# C-10l2: diagnosing rule K (10l's "X4 ctl_req fork" rows on gcd_hw)

Shard C, probe 10l2, 2026-10-29. STATUS: in progress (routes running).

## Progress log
- 07:4x: read B's Lean. Finding 1 (reading of B's constraint): what 10l calls rule K
  ("the ctl pulse at the join has ended before s can change there") is NOT B's X4
  obligation. B's X4 (`bd_mux.isochronic_forks`) says the ctl_req -> {uj0, uj1} fork needs
  NO condition under FIFO branches (`OpsCounter.mux_ok_noskew`; `mux_needs_iso_cr` is
  untimed and only bites when a wire branch can carry a runt). The condition 10l checks is
  B's X3 hold half, `bd_mux.bundled_s_hold` (`MuxEnv.H_S_PIN0/1` in OpsTimedMux, exact per
  join in LibGapMux): `Cf + pc_k.hi <= S1 + ps_k.lo`, with pc/ps INCLUDING the join's
  per-pin LUT arcs I1->O6 / I2->O6.
- Routes: no gcd_hw SDF on disk (tcheck/build is gone). Re-routing seeds d 2 3 4 with
  formal/tools/rulek/route.sh (copy of tcheck/route.sh). tcheck copied from git HEAD
  16e798d into formal/tools/rulek/tc (10m edits the live one), built, self-tests ok.
- 08:2x: seed d re-routed (nextpnr 9c732bc6303458df, toolchain.sh ok). tcheck HEAD front end
  + current rules10l rule K with the old 10l2's ablation hooks (K10L_ABLATE=1):
  K (current: (C,1) max node + select-latch max node + own latch outputs blocked in phase 0)
  passes 42/42 rows in all six corner variants (min sdf 7250, slowG 1938 ps).
  Knocmax (no (C,1) max node) fails 6/22/14/18/24/24 rows; the 10l code as committed at
  3f8eed9 (run verbatim from tc_3f8/) gives EXACTLY the Knocmax numbers. So summary10l's
  failures are a front-end artefact: see Diagnosis.
- Lean: Formal/Timing/RuleK.lean compiles (sel_fall_after_ctl_fall, ruleK_hold,
  mux_joins_ruleK, ruleK_exact, witness).
