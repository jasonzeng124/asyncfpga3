## eventgraph, corner worst

- c0 critical: 38434 ps, 88 arcs, stages ulink_n13 1190/1190, ulink_n14__1 15559/15559, umux1 3261/1675; polarity changes ulink_n13R->ulink_n14__1F, ulink_n13F->ulink_n14__1R

| line | n | ps (ps/el) | on cycle R/F | set by | margin | launch -> capture | data: logic / latch / enable / wire / ctl | en spread | req: total / not line / wire | guard | n_need | n_logic | corner_audit proposal | widest data wire | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ulink_n14__1.many.stage[1].u.rdly | 36 | 14490 (412) | 15020/15020 | E depends | 14031 | ulink_n14__1.many.stage[1].u.ctl.u.u -> umux1.uj1/A1 | 0 / 68 / 186 / 733 / 0 |  | 15514 / 494 / 494 | 0.97/1.03 | 2 | 0 | 36 | ulink_n14__1.many.stage[1].u.lat.odd.u/O6 -> umux1.uj1/A1 733 | select link (withdrawn select rule; corner_audit never shortens it); corner_audit: select path: never shortened (see docstring) |
| umux1.udly | 5 | 1728 (416) | 2151/565 | A own | 2098 | umux1.uj0 -> umux1.uxa.u/O6 | 0 / 0 / 0 / 382 / 68 |  | 2598 / 447 / 379 | 50 | 1 | 0 | 5 | umux1.uj0/O6 -> umux1.uxa.u/A3 382 | F (own flush) margin 2775; mux delay (withdrawn select rule; corner_audit never shortens it); rule A pairs by common source umux1.uj0; 32 peer output(s) no common source pairs with the request, on NO rule-A constraint: umux1.udat; corner_audit: select path: never shortened (see docstring) |
| ulink_n13.uack | 1 | 62 (374) | 614/614 | H own | 1227 |  ->  |  /  /  /  /  | 223-1026 (32 bits) | 2378 /  /  |  | 0 |  | 1 |  | corner_audit: floor 1; totals only (H) |
