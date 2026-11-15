## eventgraph, corner nom

- c0 critical: 36268 ps, 88 arcs, stages ulink_n13 1353/1353, ulink_n14__1 14644/14644, umux1 2721/1553; polarity changes ulink_n13R->ulink_n14__1F, ulink_n13F->ulink_n14__1R

| line | n | ps (ps/el) | on cycle R/F | set by | margin | launch -> capture | data: logic / latch / enable / wire / ctl | en spread | req: total / not line / wire | guard | n_need | n_logic | corner_audit proposal | widest data wire | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ulink_n14__1.many.stage[1].u.rdly | 36 | 15128 (430) | 14171/14171 | E depends | 15065 | ulink_n14__1.many.stage[1].u.ctl.u.u -> umux1.uj1/A5 | 0 / 68 / 183 / 322 / 0 |  | 16140 / 459 / 459 | 0.97/1.03 | 1 | 0 | 36 | ulink_n14__1.many.stage[1].u.lat.odd.u/O6 -> umux1.uj1/A5 322 | select link (withdrawn select rule; corner_audit never shortens it); corner_audit: select path: never shortened (see docstring) |
| umux1.udly | 5 | 1573 (376) | 1662/494 | A own | 1787 | umux1.uj0 -> umux1.uxa.u/O6 | 0 / 0 / 0 / 396 / 68 |  | 2301 / 461 / 393 | 50 | 1 | 0 | 5 | umux1.uj0/O6 -> umux1.uxa.u/A3 396 | F (own flush) margin 2918; mux delay (withdrawn select rule; corner_audit never shortens it); rule A pairs by common source umux1.uj0; 32 peer output(s) no common source pairs with the request, on NO rule-A constraint: umux1.udat; corner_audit: select path: never shortened (see docstring) |
| ulink_n13.uack | 1 | 68 (413) | 542/542 | H own | 1367 |  ->  |  /  /  /  /  | 223-871 (32 bits) | 2363 /  /  |  | 0 |  | 1 |  | corner_audit: floor 1; totals only (H) |
