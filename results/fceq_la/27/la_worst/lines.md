## eventgraph, corner worst

- c0 critical: 35576 ps, 88 arcs, stages ulink_n14__1 14404/14404, umux1 3058/1496, ulink_n13 1107/1107; polarity changes ulink_n13R->ulink_n14__1F, ulink_n13F->ulink_n14__1R

| line | n | ps (ps/el) | on cycle R/F | set by | margin | launch -> capture | data: logic / latch / enable / wire / ctl | en spread | req: total / not line / wire | guard | n_need | n_logic | corner_audit proposal | widest data wire | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ulink_n14__1.many.stage[1].u.rdly | 36 | 13460 (383) | 13870/13870 | E depends | 13373 | ulink_n14__1.many.stage[1].u.ctl.u.u -> umux1.uj1/A5 | 0 / 68 / 171 / 339 / 0 |  | 14401 / 531 / 531 | 0.97/1.03 | 1 | 0 | 36 | ulink_n14__1.many.stage[1].u.lat.odd.u/O6 -> umux1.uj1/A5 339 | select link (withdrawn select rule; corner_audit never shortens it); corner_audit: select path: never shortened (see docstring) |
| umux1.udly | 5 | 1598 (384) | 2124/562 | A own | 1877 | umux1.uj1 -> umux1.uya.u/O6 | 0 / 0 / 0 / 464 / 68 |  | 2459 / 335 / 267 | 50 | 1 | 0 | 5 | umux1.uj1/O6 -> umux1.uya.u/A2 464 | F (own flush) margin 2465; mux delay (withdrawn select rule; corner_audit never shortens it); rule A pairs by common source umux1.uj1; 32 peer output(s) no common source pairs with the request, on NO rule-A constraint: umux1.udat; corner_audit: select path: never shortened (see docstring) |
| ulink_n13.uack | 1 | 62 (374) | 583/583 | H own | 1123 |  ->  |  /  /  /  /  | 215-910 (32 bits) | 2158 /  /  |  | 0 |  | 1 |  | corner_audit: floor 1; totals only (H) |
