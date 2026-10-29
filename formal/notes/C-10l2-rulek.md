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
