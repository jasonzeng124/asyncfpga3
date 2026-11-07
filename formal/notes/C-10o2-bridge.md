# C-10o2: from 10o's timed `Settled` to O4's H_CHAIN_SETTLED (track 10/8)

Shard C, probe 10o2, 2026-10-29. WORK IN PROGRESS (skeleton saved early; see below).

Plan: (1) bridge `ChainSettle.Settled` (BoundedDelay, exact) -> `CellBind.Ops.GenChain`
through the inertial refinement (8d's `Inertial`); (2) Lean executable checker for `Lc`
(replaces chainck's Python interval code), run on gcd_hw seed d; (3) gcd s4 cm12 slowG -589.

## Progress (12:00)
- Checked (./check.sh OK): Formal/Timing/ChainSettleBridge.lean (InRun, pin_si, phase_nolag,
  phase_rise, lumped_pulse, lumped_of_forced, mono in T), ChainSettleExe.lean (checker,
  sets_sound/complete, exact_sound, gap_runt, bridge_sound), ChainSettleBridgeO4.lean
  (genChain_iff, genChain_of_forced(_or), genChain_of_check(_or)), ChainSettleBridgeWit.lean
  (bridge_witness, settled_not_genChain).
- Running: chainck2 extraction on gcd_hw seed d, then gen_lean.py -> data + decided verdicts.
