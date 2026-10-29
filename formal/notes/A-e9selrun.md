# A-e9selrun (probe E9SelRun, shard A): running design_verdict9_selL, and a junction-anchored lag

STATUS (2026-10-29, start): IN PROGRESS. Nothing claimed yet.

Plan:
1. Own copy of the generator under formal/tools-A/xaudit/selrun/: emit ackOK / ReqLine / AckLine
   data per select literal; executable Formal/Core/XAudit/Events9SelLMain.lean evaluating selL's
   checked rows; run 16 gcd_hw rows (4 seeds x slow/fast/gb/indep, E8Mux bands); negative
   controls NEGack (wrong ack wire must be rejected) and a 2-token ReqLine walk.
2. Formal/Core/XAudit/Events9SelJ.lean: junction-anchored lag (min over arms + unshared spread)
   proved from the prefix verdict; rerun.
