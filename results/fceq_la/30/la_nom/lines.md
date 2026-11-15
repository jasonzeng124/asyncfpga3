## eventgraph, corner nom

- c0 critical: 35063 ps, 88 arcs, stages ulink_n13 1383/1383, ulink_n14__1 14186/14186, umux1 2573/1352; polarity changes ulink_n13R->ulink_n14__1F, ulink_n13F->ulink_n14__1R

| line | n | ps (ps/el) | on cycle R/F | set by | margin | launch -> capture | data: logic / latch / enable / wire / ctl | en spread | req: total / not line / wire | guard | n_need | n_logic | corner_audit proposal | widest data wire | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ulink_n14__1.many.stage[1].u.rdly | 36 | 14867 (423) | 13744/13744 | E depends | 14458 | ulink_n14__1.many.stage[1].u.ctl.u.u -> umux1.uj1/A5 | 0 / 68 / 183 / 291 / 0 |  | 15481 / 260 / 260 | 0.97/1.03 | 1 | 0 | 36 | ulink_n14__1.many.stage[1].u.lat.odd.u/O6 -> umux1.uj1/A5 291 | select link (withdrawn select rule; corner_audit never shortens it); corner_audit: select path: never shortened (see docstring) |
| umux1.udly | 5 | 1575 (377) | 1683/462 | A own | 1814 | umux1.uj0 -> umux1.uxa.u/O6 | 0 / 0 / 0 / 357 / 68 |  | 2289 / 433 / 365 | 50 | 1 | 0 | 5 | umux1.uj0/O6 -> umux1.uxa.u/A2 357 | F (own flush) margin 2823; mux delay (withdrawn select rule; corner_audit never shortens it); rule A pairs by common source umux1.uj0; 32 peer output(s) no common source pairs with the request, on NO rule-A constraint: umux1.udat; corner_audit: select path: never shortened (see docstring) |
| ulink_n13.uack | 1 | 68 (414) | 665/665 | H own | 1477 |  ->  |  /  /  /  /  | 252-997 (32 bits) | 2599 /  /  |  | 0 |  | 1 |  | corner_audit: floor 1; totals only (H) |
