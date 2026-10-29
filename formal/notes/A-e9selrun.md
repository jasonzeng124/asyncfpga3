# A-e9selrun (probe E9SelRun, shard A): running design_verdict9_selL, and a junction-anchored lag

STATUS (2026-10-29, start): IN PROGRESS. Nothing claimed yet.

Plan:
1. Own copy of the generator under formal/tools-A/xaudit/selrun/: emit ackOK / ReqLine / AckLine
   data per select literal; executable Formal/Core/XAudit/Events9SelLMain.lean evaluating selL's
   checked rows; run 16 gcd_hw rows (4 seeds x slow/fast/gb/indep, E8Mux bands); negative
   controls NEGack (wrong ack wire must be rejected) and a 2-token ReqLine walk.
2. Formal/Core/XAudit/Events9SelJ.lean: junction-anchored lag (min over arms + unshared spread)
   proved from the prefix verdict; rerun.

## Early findings (11:15 UTC)
- E8Mux certificates (cert8.py, XA_ARB=old) are reproduced byte-identically by cert8.py with
  XA_ARB=old (all keys equal), so the E8SelC map indices stay valid for a regenerated log.
- **ackOK (E8Causal) cannot hold for most gcd_hw select literals**: on seed d 85 of 126 request
  wires are the end of an asymmetric (fast-fall) delay line made of 2-input AND LUTs
  (`ucmpiK.udly.chain.g[m]` = AND(link request, previous element), INIT 1000), and 8 acknowledge
  wires are an OR (`ulink_nX.uack.chain.g[1]` = OR(chain g[0], ctl), INIT 1110). `ackOK` asks
  for a chain of 1-input buffers, so these literals are rejected by design_verdict9_selL as it
  stands. Plan: a generalised identity check with AND/OR trees (Events9SelL.lean).
