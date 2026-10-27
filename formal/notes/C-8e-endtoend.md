# C-8e: end to end, checker accepts the routed pipe => FIFO (tracks 8 + 10)

Status: IN PROGRESS (notes first). Plan:
- `Formal/Net/EndToEndRace.lean`: two-path race netlists (`fan2`) and
  `race2_sound`: 10a's `check` on a fan netlist bounds the real path sums of
  every fixed-delay assignment inside the intervals (via a step-launch FixedRun
  and `check_sound`).
- `Formal/Net/EndToEnd.lean`: timed pipeline model (fixed per-arc pin delays,
  real bd_c2n INIT on the pins, LUT latch with enable/data pin delays), the
  count-based refinement to 8a's node-level model, the obligations from the
  checker, and `end_to_end`.
- `Formal/Net/EndToEndToy.lean`: 2-stage toy accepted; SDELAY-less toy rejected
  for every (m, h); a concrete run of the rejected route that corrupts token 0.
