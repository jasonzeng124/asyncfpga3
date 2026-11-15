## eventgraph, corner worst

- c0 critical: 36774 ps, 88 arcs, stages ulink_n13 999/999, ulink_n14__1 14894/14894, umux1 3217/1771; polarity changes ulink_n13R->ulink_n14__1F, ulink_n13F->ulink_n14__1R

| line | n | ps (ps/el) | on cycle R/F | set by | margin | launch -> capture | data: logic / latch / enable / wire / ctl | en spread | req: total / not line / wire | guard | n_need | n_logic | corner_audit proposal | widest data wire | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ulink_n14__1.many.stage[1].u.rdly | 36 | 14101 (401) | 14348/14348 | E depends | 13566 | ulink_n14__1.many.stage[1].u.ctl.u.u -> umux1.uj1/A1 | 0 / 68 / 169 / 696 / 0 |  | 14977 / 629 / 629 | 0.97/1.03 | 1 | 0 | 36 | ulink_n14__1.many.stage[1].u.lat.odd.u/O6 -> umux1.uj1/A1 696 | select link (withdrawn select rule; corner_audit never shortens it); corner_audit: select path: never shortened (see docstring) |
| umux1.udly | 5 | 1304 (310) | 1972/526 | A own | 1739 | umux1.uj0 -> umux1.uxa.u/O6 | 0 / 0 / 0 / 566 / 68 |  | 2423 / 451 / 383 | 50 | 1 | 0 | 5 | umux1.uj0/O6 -> umux1.uxa.u/A1 566 | F (own flush) margin 2367; mux delay (withdrawn select rule; corner_audit never shortens it); rule A pairs by common source umux1.uj0; 32 peer output(s) no common source pairs with the request, on NO rule-A constraint: umux1.udat; corner_audit: select path: never shortened (see docstring) |
| ulink_n13.uack | 1 | 62 (366) | 473/473 | H own | 1272 |  ->  |  /  /  /  /  | 171-921 (32 bits) | 2318 /  /  |  | 0 |  | 1 |  | corner_audit: floor 1; totals only (H) |
