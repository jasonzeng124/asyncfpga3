# A-e8selc (probe E8SelC): select-wire premises of the routed verdict (shard A)

STATUS (2026-10-29 09:25 UTC): started. Nothing claimed yet.

Plan:
1. `Formal/Core/XAudit/Events9Sel.lean`: `design_verdict9_sel` = design_verdict9 with SelOK at
   every real filtered pin replaced by B's H_S_STABLE + setup on the select wires (port of
   Events8BridgeSel.design_verdict8_sel), so HDsub stays discharged.
2. Compose the select-wire premise with C's H_BUNDLE / H_LATCH_HOLD: which C hypothesis, which
   channel, which A wire; channel -> wire map as data + a checked consistency predicate.
3. Hold half: a checker over the corrected bands (tools-A/xaudit/e8mux/) computing per select pin
   the hold margin, proved sound against B's hold condition; run on 4 seeds x slow/fast/gb/indep.
