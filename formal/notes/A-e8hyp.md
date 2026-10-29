# A-e8hyp (probe E8Hyp): design_verdict8's hypotheses vs shards B and C

STATUS (started 2026-10-29): in progress. Nothing claimed yet.

## Plan
1. Read the exact Lean statements of SatPin, h0/h1/hrst, HARB7, SelOK, SelPart (Events2PinDesign,
   Events7Beh, Events7Core, Events7Excl).
2. For each, find the closest B (Formal/Cells) / C (Formal/Net, Formal/Timing) theorem; write a Lean
   bridge (Formal/Core/XAudit/Events8Bridge.lean) or the exact gap (time origin, pin reading,
   corner model).
3. Joint non-vacuity witness for design_verdict8's hypotheses.
4. Mapping table for gcd_hw_hypotheses.md's A rows.
