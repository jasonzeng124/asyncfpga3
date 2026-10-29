# A-e8selc (probe E8SelC): select-wire premises of the routed verdict (shard A)

STATUS (2026-10-29 ~09:55 UTC): in progress. Lean files written, being compiled; runs pending.

Plan / files:
1. `Formal/Core/XAudit/Events9Sel.lean`: `design_verdict9_sel` (task 1). Compiled OK (overlay).
2. `Formal/Core/XAudit/Events9SelC.lean`: C channel -> A wire map, H_BUNDLE -> select stability,
   `design_verdict9_selC` (task 2).
3. `Formal/Core/XAudit/Events9SelHold.lean`: hold band check + soundness, `design_verdict9_selH`
   (task 3); `Formal/Core/XAudit/Events9SelMain.lean`: the `xselhold` executable.
4. `tools-A/xaudit/selhold/mkmap.py` (untrusted map builder), `run.sh` (16 rows).
