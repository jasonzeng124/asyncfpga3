## eventgraph, corner worst

- c0 critical: 36989 ps, 88 arcs, stages ulink_n13 1188/1188, ulink_n14__1 15095/15095, umux1 2929/1494; polarity changes ulink_n13R->ulink_n14__1F, ulink_n13F->ulink_n14__1R

| line | n | ps (ps/el) | on cycle R/F | set by | margin | launch -> capture | data: logic / latch / enable / wire / ctl | en spread | req: total / not line / wire | guard | n_need | n_logic | corner_audit proposal | widest data wire | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ulink_n14__1.many.stage[1].u.rdly | 36 | 14442 (411) | 14751/14751 | E depends | 13651 | ulink_n14__1.many.stage[1].u.ctl.u.u -> umux1.uj1/A1 | 0 / 68 / 183 / 706 / 0 |  | 15090 / 339 / 339 | 0.97/1.03 | 2 | 0 | 36 | ulink_n14__1.many.stage[1].u.lat.odd.u/O6 -> umux1.uj1/A1 706 | select link (withdrawn select rule; corner_audit never shortens it); corner_audit: select path: never shortened (see docstring) |
| umux1.udly | 5 | 1567 (376) | 1913/478 | A own | 1863 | umux1.uj1 -> umux1.uya.u/O6 | 0 / 0 / 0 / 541 / 68 |  | 2522 / 609 / 541 | 50 | 1 | 0 | 5 | umux1.uj1/O6 -> umux1.uya.u/A1 541 | F (own flush) margin 2611; mux delay (withdrawn select rule; corner_audit never shortens it); rule A pairs by common source umux1.uj1; 32 peer output(s) no common source pairs with the request, on NO rule-A constraint: umux1.udat; corner_audit: select path: never shortened (see docstring) |
| ulink_n13.uack | 1 | 62 (379) | 677/677 | H own | 975 |  ->  |  /  /  /  /  | 391-883 (32 bits) | 1984 /  /  |  | 0 |  | 1 |  | corner_audit: floor 1; totals only (H) |
